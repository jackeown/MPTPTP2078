%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:31 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  332 (2333 expanded)
%              Number of clauses        :  238 ( 875 expanded)
%              Number of leaves         :   28 ( 514 expanded)
%              Depth                    :   30
%              Number of atoms          :  951 (12054 expanded)
%              Number of equality atoms :  509 (1873 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f60,plain,(
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
     => ( ( ~ m1_subset_1(k2_partfun1(X0,X3,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(k2_partfun1(X0,X3,sK5,X1),X1,X2)
          | ~ v1_funct_1(k2_partfun1(X0,X3,sK5,X1)) )
        & r1_tarski(k7_relset_1(X0,X3,sK5,X1),X2)
        & r1_tarski(X1,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK5,X0,X3)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
          ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
            | ~ v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3)
            | ~ v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2)) )
          & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3)
          & r1_tarski(sK2,sK1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
          & v1_funct_2(X4,sK1,sK4)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) )
    & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    & v1_funct_2(sK5,sK1,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f46,f60,f59])).

fof(f102,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    inference(cnf_transformation,[],[f61])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,(
    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f103,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f101,plain,(
    v1_funct_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f99,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f105,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f109,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1749,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1752,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3471,plain,
    ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1752])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_3857,plain,
    ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3471,c_45])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1754,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4506,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_1754])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4745,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4506,c_45,c_47])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1758,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4754,plain,
    ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4745,c_1758])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1755,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1766,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1756,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4096,plain,
    ( k7_relset_1(sK1,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1749,c_1756])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1751,plain,
    ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4181,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4096,c_1751])).

cnf(c_39,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1750,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1757,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3486,plain,
    ( k1_relset_1(sK1,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1749,c_1757])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_687,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | k1_relset_1(sK1,sK4,sK5) = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_689,plain,
    ( k1_relset_1(sK1,sK4,sK5) = sK1
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_40])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_536,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_43])).

cnf(c_1030,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1817,plain,
    ( sK4 != X0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1927,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_1029,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1994,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_2019,plain,
    ( k1_relset_1(sK1,sK4,sK5) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_536,c_1927,c_1994])).

cnf(c_3489,plain,
    ( k1_relat_1(sK5) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3486,c_2019])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1759,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4555,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_1759])).

cnf(c_2550,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1758])).

cnf(c_4635,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k1_relat_1(k7_relat_1(sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4555,c_2550])).

cnf(c_4636,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4635])).

cnf(c_4644,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1750,c_4636])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1761,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2985,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_2550,c_1761])).

cnf(c_4880,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1757])).

cnf(c_27986,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,X2)) = k1_relat_1(k7_relat_1(sK5,X2))
    | r1_tarski(k9_relat_1(sK5,X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK5,X2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_4880])).

cnf(c_28568,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = k1_relat_1(k7_relat_1(sK5,sK2))
    | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4644,c_27986])).

cnf(c_28591,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
    | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28568,c_4644])).

cnf(c_28708,plain,
    ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4181,c_28591])).

cnf(c_28716,plain,
    ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4754,c_28708])).

cnf(c_28776,plain,
    ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1766,c_28716])).

cnf(c_31,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_671,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_1741,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_672,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1830,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1831,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_2081,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | k1_xboole_0 = sK3
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_45,c_47,c_672,c_1831])).

cnf(c_2082,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2081])).

cnf(c_3863,plain,
    ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) != sK2
    | sK3 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3857,c_2082])).

cnf(c_31660,plain,
    ( sK3 = k1_xboole_0
    | sK2 != sK2
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28776,c_3863])).

cnf(c_31756,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_31660])).

cnf(c_31759,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_31756])).

cnf(c_31760,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31759,c_4644])).

cnf(c_31761,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK5,sK2),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31760,c_2985])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2189,plain,
    ( ~ r2_hidden(sK0(X0,sK2),sK2)
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_10630,plain,
    ( ~ r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_10633,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2) != iProver_top
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10630])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2190,plain,
    ( r2_hidden(sK0(X0,sK2),X0)
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10628,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_10637,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2) = iProver_top
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10628])).

cnf(c_31849,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31761,c_4181,c_10633,c_10637])).

cnf(c_31854,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4754,c_31849])).

cnf(c_32001,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31854,c_4181])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1764,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4874,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1764])).

cnf(c_24661,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_4874])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_14])).

cnf(c_560,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_22])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_560])).

cnf(c_1746,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_2918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1746])).

cnf(c_4872,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1755])).

cnf(c_5006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_4872])).

cnf(c_24678,plain,
    ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24661,c_2918,c_5006])).

cnf(c_24679,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_24678])).

cnf(c_24690,plain,
    ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_24679])).

cnf(c_25090,plain,
    ( r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top
    | r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24690,c_4754])).

cnf(c_25091,plain,
    ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_25090])).

cnf(c_32093,plain,
    ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_32001,c_25091])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4873,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1755])).

cnf(c_5341,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_4873])).

cnf(c_6931,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top
    | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
    | m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5341,c_4754])).

cnf(c_6932,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6931])).

cnf(c_6940,plain,
    ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK5,sK2),X0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4644,c_6932])).

cnf(c_6962,plain,
    ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_6940])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_16])).

cnf(c_581,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_22])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_581])).

cnf(c_1745,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_2470,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1745])).

cnf(c_7460,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),X0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6962,c_2470])).

cnf(c_7470,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),X0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7460,c_2985])).

cnf(c_1769,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_322,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_323,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_396,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_323])).

cnf(c_540,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_396])).

cnf(c_541,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_1747,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_2539,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_1747])).

cnf(c_2605,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_2539])).

cnf(c_4645,plain,
    ( k1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2605,c_4636])).

cnf(c_4815,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4645,c_1759])).

cnf(c_4770,plain,
    ( v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4754])).

cnf(c_23928,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4815,c_4770])).

cnf(c_23929,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_23928])).

cnf(c_23944,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),k9_relat_1(sK5,sK2))) = k9_relat_1(sK5,sK2)
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7470,c_23929])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_132,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_133,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_135,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_134,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_136,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_1901,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1902,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1901])).

cnf(c_1970,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1974,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1970])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_639,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_1743,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_1773,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1743,c_8])).

cnf(c_2334,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1773,c_45,c_47,c_1831])).

cnf(c_2335,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2334])).

cnf(c_2348,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2814,plain,
    ( r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)))
    | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2821,plain,
    ( r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) = iProver_top
    | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_2849,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3013,plain,
    ( r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2)
    | r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3017,plain,
    ( r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2) = iProver_top
    | r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3013])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1936,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3058,plain,
    ( ~ r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2)
    | ~ r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)))
    | sK2 = k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_3059,plain,
    ( sK2 = k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))
    | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3058])).

cnf(c_2972,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != X0
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_4088,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_2972])).

cnf(c_4145,plain,
    ( ~ r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)))
    | ~ r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_4146,plain,
    ( r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) != iProver_top
    | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4145])).

cnf(c_3748,plain,
    ( X0 != X1
    | k2_partfun1(sK1,sK4,sK5,sK2) != X1
    | k2_partfun1(sK1,sK4,sK5,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_6417,plain,
    ( X0 != k7_relat_1(sK5,sK2)
    | k2_partfun1(sK1,sK4,sK5,sK2) = X0
    | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2) ),
    inference(instantiation,[status(thm)],[c_3748])).

cnf(c_6418,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
    | k2_partfun1(sK1,sK4,sK5,sK2) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(sK5,sK2) ),
    inference(instantiation,[status(thm)],[c_6417])).

cnf(c_1765,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3032,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_2918])).

cnf(c_1767,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3784,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2605,c_1767])).

cnf(c_6568,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3032,c_3784])).

cnf(c_6615,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6568])).

cnf(c_1825,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_6991,plain,
    ( sK2 != k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_7104,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_7105,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7104])).

cnf(c_7107,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7105])).

cnf(c_4400,plain,
    ( k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_7577,plain,
    ( k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(X0)
    | k1_xboole_0 != k1_relat_1(X0)
    | k1_xboole_0 = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_4400])).

cnf(c_7578,plain,
    ( k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7577])).

cnf(c_7731,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_8147,plain,
    ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_8148,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8147])).

cnf(c_8211,plain,
    ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_2061,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_8401,plain,
    ( ~ r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_8402,plain,
    ( r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8401])).

cnf(c_8982,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK1,sK4,sK5,sK2) = k7_relat_1(sK5,sK2) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_9050,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_9051,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9050])).

cnf(c_7458,plain,
    ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6962,c_1764])).

cnf(c_9129,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7458,c_3784])).

cnf(c_1031,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_14265,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X2)
    | X2 != X1
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_14267,plain,
    ( r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14265])).

cnf(c_14266,plain,
    ( X0 != X1
    | k2_partfun1(sK1,sK4,sK5,sK2) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14265])).

cnf(c_14268,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14266])).

cnf(c_18113,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_4590,plain,
    ( k1_relset_1(X0,X1,X2) != X3
    | k1_xboole_0 != X3
    | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_11494,plain,
    ( k1_relset_1(X0,X1,X2) != k1_relat_1(X2)
    | k1_xboole_0 = k1_relset_1(X0,X1,X2)
    | k1_xboole_0 != k1_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_4590])).

cnf(c_18167,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_xboole_0 = k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_xboole_0 != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_11494])).

cnf(c_1036,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_18617,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_18618,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18617])).

cnf(c_4292,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),X2)
    | X2 != X1
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_20048,plain,
    ( r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),X0)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),X1)
    | X0 != X1
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_4292])).

cnf(c_20049,plain,
    ( X0 != X1
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),X0) = iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20048])).

cnf(c_20051,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20049])).

cnf(c_21318,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(X0))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_21319,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21318])).

cnf(c_21321,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21319])).

cnf(c_1034,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_21332,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_21333,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21332])).

cnf(c_23858,plain,
    ( X0 != X1
    | X0 = k7_relat_1(sK5,sK2)
    | k7_relat_1(sK5,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_23859,plain,
    ( k7_relat_1(sK5,sK2) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK5,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23858])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2429,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_3738,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(k7_relat_1(sK5,sK2),X2)
    | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != X2 ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_23872,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_3738])).

cnf(c_23873,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2)
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23872])).

cnf(c_23875,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_23873])).

cnf(c_24520,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23944,c_42,c_40,c_132,c_133,c_135,c_136,c_1901,c_1902,c_1970,c_1974,c_2335,c_2348,c_2821,c_2849,c_3017,c_3059,c_4088,c_4146,c_6418,c_6615,c_6962,c_6991,c_7107,c_7578,c_7731,c_8147,c_8148,c_8211,c_8402,c_8982,c_9051,c_9129,c_14267,c_14268,c_18113,c_18167,c_18618,c_20051,c_21321,c_21333,c_23859,c_23875])).

cnf(c_6555,plain,
    ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4644,c_3032])).

cnf(c_6579,plain,
    ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6555])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32093,c_24520,c_6579])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:53:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.68/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/1.98  
% 11.68/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.68/1.98  
% 11.68/1.98  ------  iProver source info
% 11.68/1.98  
% 11.68/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.68/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.68/1.98  git: non_committed_changes: false
% 11.68/1.98  git: last_make_outside_of_git: false
% 11.68/1.98  
% 11.68/1.98  ------ 
% 11.68/1.98  
% 11.68/1.98  ------ Input Options
% 11.68/1.98  
% 11.68/1.98  --out_options                           all
% 11.68/1.98  --tptp_safe_out                         true
% 11.68/1.98  --problem_path                          ""
% 11.68/1.98  --include_path                          ""
% 11.68/1.98  --clausifier                            res/vclausify_rel
% 11.68/1.98  --clausifier_options                    ""
% 11.68/1.98  --stdin                                 false
% 11.68/1.98  --stats_out                             all
% 11.68/1.98  
% 11.68/1.98  ------ General Options
% 11.68/1.98  
% 11.68/1.98  --fof                                   false
% 11.68/1.98  --time_out_real                         305.
% 11.68/1.98  --time_out_virtual                      -1.
% 11.68/1.98  --symbol_type_check                     false
% 11.68/1.98  --clausify_out                          false
% 11.68/1.98  --sig_cnt_out                           false
% 11.68/1.98  --trig_cnt_out                          false
% 11.68/1.98  --trig_cnt_out_tolerance                1.
% 11.68/1.98  --trig_cnt_out_sk_spl                   false
% 11.68/1.98  --abstr_cl_out                          false
% 11.68/1.98  
% 11.68/1.98  ------ Global Options
% 11.68/1.98  
% 11.68/1.98  --schedule                              default
% 11.68/1.98  --add_important_lit                     false
% 11.68/1.98  --prop_solver_per_cl                    1000
% 11.68/1.98  --min_unsat_core                        false
% 11.68/1.98  --soft_assumptions                      false
% 11.68/1.98  --soft_lemma_size                       3
% 11.68/1.98  --prop_impl_unit_size                   0
% 11.68/1.98  --prop_impl_unit                        []
% 11.68/1.98  --share_sel_clauses                     true
% 11.68/1.98  --reset_solvers                         false
% 11.68/1.98  --bc_imp_inh                            [conj_cone]
% 11.68/1.98  --conj_cone_tolerance                   3.
% 11.68/1.98  --extra_neg_conj                        none
% 11.68/1.98  --large_theory_mode                     true
% 11.68/1.98  --prolific_symb_bound                   200
% 11.68/1.98  --lt_threshold                          2000
% 11.68/1.98  --clause_weak_htbl                      true
% 11.68/1.98  --gc_record_bc_elim                     false
% 11.68/1.98  
% 11.68/1.98  ------ Preprocessing Options
% 11.68/1.98  
% 11.68/1.98  --preprocessing_flag                    true
% 11.68/1.98  --time_out_prep_mult                    0.1
% 11.68/1.98  --splitting_mode                        input
% 11.68/1.98  --splitting_grd                         true
% 11.68/1.98  --splitting_cvd                         false
% 11.68/1.98  --splitting_cvd_svl                     false
% 11.68/1.98  --splitting_nvd                         32
% 11.68/1.98  --sub_typing                            true
% 11.68/1.98  --prep_gs_sim                           true
% 11.68/1.98  --prep_unflatten                        true
% 11.68/1.98  --prep_res_sim                          true
% 11.68/1.98  --prep_upred                            true
% 11.68/1.98  --prep_sem_filter                       exhaustive
% 11.68/1.98  --prep_sem_filter_out                   false
% 11.68/1.98  --pred_elim                             true
% 11.68/1.98  --res_sim_input                         true
% 11.68/1.98  --eq_ax_congr_red                       true
% 11.68/1.98  --pure_diseq_elim                       true
% 11.68/1.98  --brand_transform                       false
% 11.68/1.98  --non_eq_to_eq                          false
% 11.68/1.98  --prep_def_merge                        true
% 11.68/1.98  --prep_def_merge_prop_impl              false
% 11.68/1.98  --prep_def_merge_mbd                    true
% 11.68/1.98  --prep_def_merge_tr_red                 false
% 11.68/1.98  --prep_def_merge_tr_cl                  false
% 11.68/1.98  --smt_preprocessing                     true
% 11.68/1.98  --smt_ac_axioms                         fast
% 11.68/1.98  --preprocessed_out                      false
% 11.68/1.98  --preprocessed_stats                    false
% 11.68/1.98  
% 11.68/1.98  ------ Abstraction refinement Options
% 11.68/1.98  
% 11.68/1.98  --abstr_ref                             []
% 11.68/1.98  --abstr_ref_prep                        false
% 11.68/1.98  --abstr_ref_until_sat                   false
% 11.68/1.98  --abstr_ref_sig_restrict                funpre
% 11.68/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/1.98  --abstr_ref_under                       []
% 11.68/1.98  
% 11.68/1.98  ------ SAT Options
% 11.68/1.98  
% 11.68/1.98  --sat_mode                              false
% 11.68/1.98  --sat_fm_restart_options                ""
% 11.68/1.98  --sat_gr_def                            false
% 11.68/1.98  --sat_epr_types                         true
% 11.68/1.98  --sat_non_cyclic_types                  false
% 11.68/1.98  --sat_finite_models                     false
% 11.68/1.98  --sat_fm_lemmas                         false
% 11.68/1.98  --sat_fm_prep                           false
% 11.68/1.98  --sat_fm_uc_incr                        true
% 11.68/1.98  --sat_out_model                         small
% 11.68/1.98  --sat_out_clauses                       false
% 11.68/1.98  
% 11.68/1.98  ------ QBF Options
% 11.68/1.98  
% 11.68/1.98  --qbf_mode                              false
% 11.68/1.98  --qbf_elim_univ                         false
% 11.68/1.98  --qbf_dom_inst                          none
% 11.68/1.98  --qbf_dom_pre_inst                      false
% 11.68/1.98  --qbf_sk_in                             false
% 11.68/1.98  --qbf_pred_elim                         true
% 11.68/1.98  --qbf_split                             512
% 11.68/1.98  
% 11.68/1.98  ------ BMC1 Options
% 11.68/1.98  
% 11.68/1.98  --bmc1_incremental                      false
% 11.68/1.98  --bmc1_axioms                           reachable_all
% 11.68/1.98  --bmc1_min_bound                        0
% 11.68/1.98  --bmc1_max_bound                        -1
% 11.68/1.98  --bmc1_max_bound_default                -1
% 11.68/1.98  --bmc1_symbol_reachability              true
% 11.68/1.98  --bmc1_property_lemmas                  false
% 11.68/1.98  --bmc1_k_induction                      false
% 11.68/1.98  --bmc1_non_equiv_states                 false
% 11.68/1.98  --bmc1_deadlock                         false
% 11.68/1.98  --bmc1_ucm                              false
% 11.68/1.98  --bmc1_add_unsat_core                   none
% 11.68/1.98  --bmc1_unsat_core_children              false
% 11.68/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/1.98  --bmc1_out_stat                         full
% 11.68/1.98  --bmc1_ground_init                      false
% 11.68/1.98  --bmc1_pre_inst_next_state              false
% 11.68/1.98  --bmc1_pre_inst_state                   false
% 11.68/1.98  --bmc1_pre_inst_reach_state             false
% 11.68/1.98  --bmc1_out_unsat_core                   false
% 11.68/1.98  --bmc1_aig_witness_out                  false
% 11.68/1.98  --bmc1_verbose                          false
% 11.68/1.98  --bmc1_dump_clauses_tptp                false
% 11.68/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.68/1.98  --bmc1_dump_file                        -
% 11.68/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.68/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.68/1.98  --bmc1_ucm_extend_mode                  1
% 11.68/1.98  --bmc1_ucm_init_mode                    2
% 11.68/1.98  --bmc1_ucm_cone_mode                    none
% 11.68/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.68/1.98  --bmc1_ucm_relax_model                  4
% 11.68/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.68/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/1.98  --bmc1_ucm_layered_model                none
% 11.68/1.98  --bmc1_ucm_max_lemma_size               10
% 11.68/1.98  
% 11.68/1.98  ------ AIG Options
% 11.68/1.98  
% 11.68/1.98  --aig_mode                              false
% 11.68/1.98  
% 11.68/1.98  ------ Instantiation Options
% 11.68/1.98  
% 11.68/1.98  --instantiation_flag                    true
% 11.68/1.98  --inst_sos_flag                         true
% 11.68/1.98  --inst_sos_phase                        true
% 11.68/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/1.98  --inst_lit_sel_side                     num_symb
% 11.68/1.98  --inst_solver_per_active                1400
% 11.68/1.98  --inst_solver_calls_frac                1.
% 11.68/1.98  --inst_passive_queue_type               priority_queues
% 11.68/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/1.98  --inst_passive_queues_freq              [25;2]
% 11.68/1.98  --inst_dismatching                      true
% 11.68/1.98  --inst_eager_unprocessed_to_passive     true
% 11.68/1.98  --inst_prop_sim_given                   true
% 11.68/1.98  --inst_prop_sim_new                     false
% 11.68/1.98  --inst_subs_new                         false
% 11.68/1.98  --inst_eq_res_simp                      false
% 11.68/1.98  --inst_subs_given                       false
% 11.68/1.98  --inst_orphan_elimination               true
% 11.68/1.98  --inst_learning_loop_flag               true
% 11.68/1.98  --inst_learning_start                   3000
% 11.68/1.98  --inst_learning_factor                  2
% 11.68/1.98  --inst_start_prop_sim_after_learn       3
% 11.68/1.98  --inst_sel_renew                        solver
% 11.68/1.98  --inst_lit_activity_flag                true
% 11.68/1.98  --inst_restr_to_given                   false
% 11.68/1.98  --inst_activity_threshold               500
% 11.68/1.98  --inst_out_proof                        true
% 11.68/1.98  
% 11.68/1.98  ------ Resolution Options
% 11.68/1.98  
% 11.68/1.98  --resolution_flag                       true
% 11.68/1.98  --res_lit_sel                           adaptive
% 11.68/1.98  --res_lit_sel_side                      none
% 11.68/1.98  --res_ordering                          kbo
% 11.68/1.98  --res_to_prop_solver                    active
% 11.68/1.98  --res_prop_simpl_new                    false
% 11.68/1.98  --res_prop_simpl_given                  true
% 11.68/1.98  --res_passive_queue_type                priority_queues
% 11.68/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/1.98  --res_passive_queues_freq               [15;5]
% 11.68/1.98  --res_forward_subs                      full
% 11.68/1.98  --res_backward_subs                     full
% 11.68/1.98  --res_forward_subs_resolution           true
% 11.68/1.98  --res_backward_subs_resolution          true
% 11.68/1.98  --res_orphan_elimination                true
% 11.68/1.98  --res_time_limit                        2.
% 11.68/1.98  --res_out_proof                         true
% 11.68/1.98  
% 11.68/1.98  ------ Superposition Options
% 11.68/1.98  
% 11.68/1.98  --superposition_flag                    true
% 11.68/1.98  --sup_passive_queue_type                priority_queues
% 11.68/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.68/1.98  --demod_completeness_check              fast
% 11.68/1.98  --demod_use_ground                      true
% 11.68/1.98  --sup_to_prop_solver                    passive
% 11.68/1.98  --sup_prop_simpl_new                    true
% 11.68/1.98  --sup_prop_simpl_given                  true
% 11.68/1.98  --sup_fun_splitting                     true
% 11.68/1.98  --sup_smt_interval                      50000
% 11.68/1.98  
% 11.68/1.98  ------ Superposition Simplification Setup
% 11.68/1.98  
% 11.68/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.68/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.68/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.68/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.68/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.68/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.68/1.98  --sup_immed_triv                        [TrivRules]
% 11.68/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.98  --sup_immed_bw_main                     []
% 11.68/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.68/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.98  --sup_input_bw                          []
% 11.68/1.98  
% 11.68/1.98  ------ Combination Options
% 11.68/1.98  
% 11.68/1.98  --comb_res_mult                         3
% 11.68/1.98  --comb_sup_mult                         2
% 11.68/1.98  --comb_inst_mult                        10
% 11.68/1.98  
% 11.68/1.98  ------ Debug Options
% 11.68/1.98  
% 11.68/1.98  --dbg_backtrace                         false
% 11.68/1.98  --dbg_dump_prop_clauses                 false
% 11.68/1.98  --dbg_dump_prop_clauses_file            -
% 11.68/1.98  --dbg_out_stat                          false
% 11.68/1.98  ------ Parsing...
% 11.68/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.68/1.98  
% 11.68/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.68/1.98  
% 11.68/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.68/1.98  
% 11.68/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.68/1.98  ------ Proving...
% 11.68/1.98  ------ Problem Properties 
% 11.68/1.98  
% 11.68/1.98  
% 11.68/1.98  clauses                                 36
% 11.68/1.98  conjectures                             4
% 11.68/1.98  EPR                                     7
% 11.68/1.98  Horn                                    33
% 11.68/1.98  unary                                   9
% 11.68/1.98  binary                                  14
% 11.68/1.98  lits                                    85
% 11.68/1.98  lits eq                                 26
% 11.68/1.98  fd_pure                                 0
% 11.68/1.98  fd_pseudo                               0
% 11.68/1.98  fd_cond                                 1
% 11.68/1.98  fd_pseudo_cond                          1
% 11.68/1.98  AC symbols                              0
% 11.68/1.98  
% 11.68/1.98  ------ Schedule dynamic 5 is on 
% 11.68/1.98  
% 11.68/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.68/1.98  
% 11.68/1.98  
% 11.68/1.98  ------ 
% 11.68/1.98  Current options:
% 11.68/1.98  ------ 
% 11.68/1.98  
% 11.68/1.98  ------ Input Options
% 11.68/1.98  
% 11.68/1.98  --out_options                           all
% 11.68/1.98  --tptp_safe_out                         true
% 11.68/1.98  --problem_path                          ""
% 11.68/1.98  --include_path                          ""
% 11.68/1.98  --clausifier                            res/vclausify_rel
% 11.68/1.98  --clausifier_options                    ""
% 11.68/1.98  --stdin                                 false
% 11.68/1.98  --stats_out                             all
% 11.68/1.98  
% 11.68/1.98  ------ General Options
% 11.68/1.98  
% 11.68/1.98  --fof                                   false
% 11.68/1.98  --time_out_real                         305.
% 11.68/1.98  --time_out_virtual                      -1.
% 11.68/1.98  --symbol_type_check                     false
% 11.68/1.98  --clausify_out                          false
% 11.68/1.98  --sig_cnt_out                           false
% 11.68/1.98  --trig_cnt_out                          false
% 11.68/1.98  --trig_cnt_out_tolerance                1.
% 11.68/1.98  --trig_cnt_out_sk_spl                   false
% 11.68/1.98  --abstr_cl_out                          false
% 11.68/1.98  
% 11.68/1.98  ------ Global Options
% 11.68/1.98  
% 11.68/1.98  --schedule                              default
% 11.68/1.98  --add_important_lit                     false
% 11.68/1.98  --prop_solver_per_cl                    1000
% 11.68/1.98  --min_unsat_core                        false
% 11.68/1.98  --soft_assumptions                      false
% 11.68/1.98  --soft_lemma_size                       3
% 11.68/1.98  --prop_impl_unit_size                   0
% 11.68/1.98  --prop_impl_unit                        []
% 11.68/1.98  --share_sel_clauses                     true
% 11.68/1.98  --reset_solvers                         false
% 11.68/1.98  --bc_imp_inh                            [conj_cone]
% 11.68/1.98  --conj_cone_tolerance                   3.
% 11.68/1.98  --extra_neg_conj                        none
% 11.68/1.98  --large_theory_mode                     true
% 11.68/1.98  --prolific_symb_bound                   200
% 11.68/1.98  --lt_threshold                          2000
% 11.68/1.98  --clause_weak_htbl                      true
% 11.68/1.98  --gc_record_bc_elim                     false
% 11.68/1.98  
% 11.68/1.98  ------ Preprocessing Options
% 11.68/1.98  
% 11.68/1.98  --preprocessing_flag                    true
% 11.68/1.98  --time_out_prep_mult                    0.1
% 11.68/1.98  --splitting_mode                        input
% 11.68/1.98  --splitting_grd                         true
% 11.68/1.98  --splitting_cvd                         false
% 11.68/1.98  --splitting_cvd_svl                     false
% 11.68/1.98  --splitting_nvd                         32
% 11.68/1.98  --sub_typing                            true
% 11.68/1.98  --prep_gs_sim                           true
% 11.68/1.98  --prep_unflatten                        true
% 11.68/1.98  --prep_res_sim                          true
% 11.68/1.98  --prep_upred                            true
% 11.68/1.98  --prep_sem_filter                       exhaustive
% 11.68/1.98  --prep_sem_filter_out                   false
% 11.68/1.98  --pred_elim                             true
% 11.68/1.98  --res_sim_input                         true
% 11.68/1.98  --eq_ax_congr_red                       true
% 11.68/1.98  --pure_diseq_elim                       true
% 11.68/1.98  --brand_transform                       false
% 11.68/1.98  --non_eq_to_eq                          false
% 11.68/1.98  --prep_def_merge                        true
% 11.68/1.98  --prep_def_merge_prop_impl              false
% 11.68/1.98  --prep_def_merge_mbd                    true
% 11.68/1.98  --prep_def_merge_tr_red                 false
% 11.68/1.98  --prep_def_merge_tr_cl                  false
% 11.68/1.98  --smt_preprocessing                     true
% 11.68/1.98  --smt_ac_axioms                         fast
% 11.68/1.98  --preprocessed_out                      false
% 11.68/1.98  --preprocessed_stats                    false
% 11.68/1.98  
% 11.68/1.98  ------ Abstraction refinement Options
% 11.68/1.98  
% 11.68/1.98  --abstr_ref                             []
% 11.68/1.98  --abstr_ref_prep                        false
% 11.68/1.98  --abstr_ref_until_sat                   false
% 11.68/1.98  --abstr_ref_sig_restrict                funpre
% 11.68/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/1.98  --abstr_ref_under                       []
% 11.68/1.98  
% 11.68/1.98  ------ SAT Options
% 11.68/1.98  
% 11.68/1.98  --sat_mode                              false
% 11.68/1.98  --sat_fm_restart_options                ""
% 11.68/1.98  --sat_gr_def                            false
% 11.68/1.98  --sat_epr_types                         true
% 11.68/1.98  --sat_non_cyclic_types                  false
% 11.68/1.98  --sat_finite_models                     false
% 11.68/1.98  --sat_fm_lemmas                         false
% 11.68/1.98  --sat_fm_prep                           false
% 11.68/1.98  --sat_fm_uc_incr                        true
% 11.68/1.98  --sat_out_model                         small
% 11.68/1.98  --sat_out_clauses                       false
% 11.68/1.98  
% 11.68/1.98  ------ QBF Options
% 11.68/1.98  
% 11.68/1.98  --qbf_mode                              false
% 11.68/1.98  --qbf_elim_univ                         false
% 11.68/1.98  --qbf_dom_inst                          none
% 11.68/1.98  --qbf_dom_pre_inst                      false
% 11.68/1.98  --qbf_sk_in                             false
% 11.68/1.98  --qbf_pred_elim                         true
% 11.68/1.98  --qbf_split                             512
% 11.68/1.98  
% 11.68/1.98  ------ BMC1 Options
% 11.68/1.98  
% 11.68/1.98  --bmc1_incremental                      false
% 11.68/1.98  --bmc1_axioms                           reachable_all
% 11.68/1.98  --bmc1_min_bound                        0
% 11.68/1.98  --bmc1_max_bound                        -1
% 11.68/1.98  --bmc1_max_bound_default                -1
% 11.68/1.98  --bmc1_symbol_reachability              true
% 11.68/1.98  --bmc1_property_lemmas                  false
% 11.68/1.98  --bmc1_k_induction                      false
% 11.68/1.99  --bmc1_non_equiv_states                 false
% 11.68/1.99  --bmc1_deadlock                         false
% 11.68/1.99  --bmc1_ucm                              false
% 11.68/1.99  --bmc1_add_unsat_core                   none
% 11.68/1.99  --bmc1_unsat_core_children              false
% 11.68/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/1.99  --bmc1_out_stat                         full
% 11.68/1.99  --bmc1_ground_init                      false
% 11.68/1.99  --bmc1_pre_inst_next_state              false
% 11.68/1.99  --bmc1_pre_inst_state                   false
% 11.68/1.99  --bmc1_pre_inst_reach_state             false
% 11.68/1.99  --bmc1_out_unsat_core                   false
% 11.68/1.99  --bmc1_aig_witness_out                  false
% 11.68/1.99  --bmc1_verbose                          false
% 11.68/1.99  --bmc1_dump_clauses_tptp                false
% 11.68/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.68/1.99  --bmc1_dump_file                        -
% 11.68/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.68/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.68/1.99  --bmc1_ucm_extend_mode                  1
% 11.68/1.99  --bmc1_ucm_init_mode                    2
% 11.68/1.99  --bmc1_ucm_cone_mode                    none
% 11.68/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.68/1.99  --bmc1_ucm_relax_model                  4
% 11.68/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.68/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/1.99  --bmc1_ucm_layered_model                none
% 11.68/1.99  --bmc1_ucm_max_lemma_size               10
% 11.68/1.99  
% 11.68/1.99  ------ AIG Options
% 11.68/1.99  
% 11.68/1.99  --aig_mode                              false
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation Options
% 11.68/1.99  
% 11.68/1.99  --instantiation_flag                    true
% 11.68/1.99  --inst_sos_flag                         true
% 11.68/1.99  --inst_sos_phase                        true
% 11.68/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel_side                     none
% 11.68/1.99  --inst_solver_per_active                1400
% 11.68/1.99  --inst_solver_calls_frac                1.
% 11.68/1.99  --inst_passive_queue_type               priority_queues
% 11.68/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/1.99  --inst_passive_queues_freq              [25;2]
% 11.68/1.99  --inst_dismatching                      true
% 11.68/1.99  --inst_eager_unprocessed_to_passive     true
% 11.68/1.99  --inst_prop_sim_given                   true
% 11.68/1.99  --inst_prop_sim_new                     false
% 11.68/1.99  --inst_subs_new                         false
% 11.68/1.99  --inst_eq_res_simp                      false
% 11.68/1.99  --inst_subs_given                       false
% 11.68/1.99  --inst_orphan_elimination               true
% 11.68/1.99  --inst_learning_loop_flag               true
% 11.68/1.99  --inst_learning_start                   3000
% 11.68/1.99  --inst_learning_factor                  2
% 11.68/1.99  --inst_start_prop_sim_after_learn       3
% 11.68/1.99  --inst_sel_renew                        solver
% 11.68/1.99  --inst_lit_activity_flag                true
% 11.68/1.99  --inst_restr_to_given                   false
% 11.68/1.99  --inst_activity_threshold               500
% 11.68/1.99  --inst_out_proof                        true
% 11.68/1.99  
% 11.68/1.99  ------ Resolution Options
% 11.68/1.99  
% 11.68/1.99  --resolution_flag                       false
% 11.68/1.99  --res_lit_sel                           adaptive
% 11.68/1.99  --res_lit_sel_side                      none
% 11.68/1.99  --res_ordering                          kbo
% 11.68/1.99  --res_to_prop_solver                    active
% 11.68/1.99  --res_prop_simpl_new                    false
% 11.68/1.99  --res_prop_simpl_given                  true
% 11.68/1.99  --res_passive_queue_type                priority_queues
% 11.68/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/1.99  --res_passive_queues_freq               [15;5]
% 11.68/1.99  --res_forward_subs                      full
% 11.68/1.99  --res_backward_subs                     full
% 11.68/1.99  --res_forward_subs_resolution           true
% 11.68/1.99  --res_backward_subs_resolution          true
% 11.68/1.99  --res_orphan_elimination                true
% 11.68/1.99  --res_time_limit                        2.
% 11.68/1.99  --res_out_proof                         true
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Options
% 11.68/1.99  
% 11.68/1.99  --superposition_flag                    true
% 11.68/1.99  --sup_passive_queue_type                priority_queues
% 11.68/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.68/1.99  --demod_completeness_check              fast
% 11.68/1.99  --demod_use_ground                      true
% 11.68/1.99  --sup_to_prop_solver                    passive
% 11.68/1.99  --sup_prop_simpl_new                    true
% 11.68/1.99  --sup_prop_simpl_given                  true
% 11.68/1.99  --sup_fun_splitting                     true
% 11.68/1.99  --sup_smt_interval                      50000
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Simplification Setup
% 11.68/1.99  
% 11.68/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.68/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_immed_triv                        [TrivRules]
% 11.68/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_bw_main                     []
% 11.68/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_input_bw                          []
% 11.68/1.99  
% 11.68/1.99  ------ Combination Options
% 11.68/1.99  
% 11.68/1.99  --comb_res_mult                         3
% 11.68/1.99  --comb_sup_mult                         2
% 11.68/1.99  --comb_inst_mult                        10
% 11.68/1.99  
% 11.68/1.99  ------ Debug Options
% 11.68/1.99  
% 11.68/1.99  --dbg_backtrace                         false
% 11.68/1.99  --dbg_dump_prop_clauses                 false
% 11.68/1.99  --dbg_dump_prop_clauses_file            -
% 11.68/1.99  --dbg_out_stat                          false
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  ------ Proving...
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS status Theorem for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  fof(f22,conjecture,(
% 11.68/1.99    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f23,negated_conjecture,(
% 11.68/1.99    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 11.68/1.99    inference(negated_conjecture,[],[f22])).
% 11.68/1.99  
% 11.68/1.99  fof(f45,plain,(
% 11.68/1.99    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 11.68/1.99    inference(ennf_transformation,[],[f23])).
% 11.68/1.99  
% 11.68/1.99  fof(f46,plain,(
% 11.68/1.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 11.68/1.99    inference(flattening,[],[f45])).
% 11.68/1.99  
% 11.68/1.99  fof(f60,plain,(
% 11.68/1.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK5,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK5,X1))) & r1_tarski(k7_relset_1(X0,X3,sK5,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK5,X0,X3) & v1_funct_1(sK5))) )),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f59,plain,(
% 11.68/1.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(X4,sK1,sK4) & v1_funct_1(X4)) & ~v1_xboole_0(sK4))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f61,plain,(
% 11.68/1.99    ((~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(sK5,sK1,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f46,f60,f59])).
% 11.68/1.99  
% 11.68/1.99  fof(f102,plain,(
% 11.68/1.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))),
% 11.68/1.99    inference(cnf_transformation,[],[f61])).
% 11.68/1.99  
% 11.68/1.99  fof(f21,axiom,(
% 11.68/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f43,plain,(
% 11.68/1.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.68/1.99    inference(ennf_transformation,[],[f21])).
% 11.68/1.99  
% 11.68/1.99  fof(f44,plain,(
% 11.68/1.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.68/1.99    inference(flattening,[],[f43])).
% 11.68/1.99  
% 11.68/1.99  fof(f98,plain,(
% 11.68/1.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f44])).
% 11.68/1.99  
% 11.68/1.99  fof(f100,plain,(
% 11.68/1.99    v1_funct_1(sK5)),
% 11.68/1.99    inference(cnf_transformation,[],[f61])).
% 11.68/1.99  
% 11.68/1.99  fof(f20,axiom,(
% 11.68/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f41,plain,(
% 11.68/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.68/1.99    inference(ennf_transformation,[],[f20])).
% 11.68/1.99  
% 11.68/1.99  fof(f42,plain,(
% 11.68/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.68/1.99    inference(flattening,[],[f41])).
% 11.68/1.99  
% 11.68/1.99  fof(f97,plain,(
% 11.68/1.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f42])).
% 11.68/1.99  
% 11.68/1.99  fof(f14,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f33,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.68/1.99    inference(ennf_transformation,[],[f14])).
% 11.68/1.99  
% 11.68/1.99  fof(f84,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f33])).
% 11.68/1.99  
% 11.68/1.99  fof(f18,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f37,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 11.68/1.99    inference(ennf_transformation,[],[f18])).
% 11.68/1.99  
% 11.68/1.99  fof(f38,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 11.68/1.99    inference(flattening,[],[f37])).
% 11.68/1.99  
% 11.68/1.99  fof(f89,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f38])).
% 11.68/1.99  
% 11.68/1.99  fof(f3,axiom,(
% 11.68/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f51,plain,(
% 11.68/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.68/1.99    inference(nnf_transformation,[],[f3])).
% 11.68/1.99  
% 11.68/1.99  fof(f52,plain,(
% 11.68/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.68/1.99    inference(flattening,[],[f51])).
% 11.68/1.99  
% 11.68/1.99  fof(f66,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.68/1.99    inference(cnf_transformation,[],[f52])).
% 11.68/1.99  
% 11.68/1.99  fof(f107,plain,(
% 11.68/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.68/1.99    inference(equality_resolution,[],[f66])).
% 11.68/1.99  
% 11.68/1.99  fof(f17,axiom,(
% 11.68/1.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f36,plain,(
% 11.68/1.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.68/1.99    inference(ennf_transformation,[],[f17])).
% 11.68/1.99  
% 11.68/1.99  fof(f88,plain,(
% 11.68/1.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f36])).
% 11.68/1.99  
% 11.68/1.99  fof(f104,plain,(
% 11.68/1.99    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)),
% 11.68/1.99    inference(cnf_transformation,[],[f61])).
% 11.68/1.99  
% 11.68/1.99  fof(f103,plain,(
% 11.68/1.99    r1_tarski(sK2,sK1)),
% 11.68/1.99    inference(cnf_transformation,[],[f61])).
% 11.68/1.99  
% 11.68/1.99  fof(f16,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f35,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.68/1.99    inference(ennf_transformation,[],[f16])).
% 11.68/1.99  
% 11.68/1.99  fof(f87,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f35])).
% 11.68/1.99  
% 11.68/1.99  fof(f19,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f39,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.68/1.99    inference(ennf_transformation,[],[f19])).
% 11.68/1.99  
% 11.68/1.99  fof(f40,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.68/1.99    inference(flattening,[],[f39])).
% 11.68/1.99  
% 11.68/1.99  fof(f58,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.68/1.99    inference(nnf_transformation,[],[f40])).
% 11.68/1.99  
% 11.68/1.99  fof(f90,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f58])).
% 11.68/1.99  
% 11.68/1.99  fof(f101,plain,(
% 11.68/1.99    v1_funct_2(sK5,sK1,sK4)),
% 11.68/1.99    inference(cnf_transformation,[],[f61])).
% 11.68/1.99  
% 11.68/1.99  fof(f2,axiom,(
% 11.68/1.99    v1_xboole_0(k1_xboole_0)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f65,plain,(
% 11.68/1.99    v1_xboole_0(k1_xboole_0)),
% 11.68/1.99    inference(cnf_transformation,[],[f2])).
% 11.68/1.99  
% 11.68/1.99  fof(f99,plain,(
% 11.68/1.99    ~v1_xboole_0(sK4)),
% 11.68/1.99    inference(cnf_transformation,[],[f61])).
% 11.68/1.99  
% 11.68/1.99  fof(f13,axiom,(
% 11.68/1.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f31,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f13])).
% 11.68/1.99  
% 11.68/1.99  fof(f32,plain,(
% 11.68/1.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(flattening,[],[f31])).
% 11.68/1.99  
% 11.68/1.99  fof(f83,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f32])).
% 11.68/1.99  
% 11.68/1.99  fof(f11,axiom,(
% 11.68/1.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f29,plain,(
% 11.68/1.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f11])).
% 11.68/1.99  
% 11.68/1.99  fof(f81,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f29])).
% 11.68/1.99  
% 11.68/1.99  fof(f92,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f58])).
% 11.68/1.99  
% 11.68/1.99  fof(f105,plain,(
% 11.68/1.99    ~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))),
% 11.68/1.99    inference(cnf_transformation,[],[f61])).
% 11.68/1.99  
% 11.68/1.99  fof(f96,plain,(
% 11.68/1.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f42])).
% 11.68/1.99  
% 11.68/1.99  fof(f1,axiom,(
% 11.68/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f24,plain,(
% 11.68/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.68/1.99    inference(ennf_transformation,[],[f1])).
% 11.68/1.99  
% 11.68/1.99  fof(f47,plain,(
% 11.68/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.68/1.99    inference(nnf_transformation,[],[f24])).
% 11.68/1.99  
% 11.68/1.99  fof(f48,plain,(
% 11.68/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.68/1.99    inference(rectify,[],[f47])).
% 11.68/1.99  
% 11.68/1.99  fof(f49,plain,(
% 11.68/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f50,plain,(
% 11.68/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 11.68/1.99  
% 11.68/1.99  fof(f64,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f50])).
% 11.68/1.99  
% 11.68/1.99  fof(f63,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f50])).
% 11.68/1.99  
% 11.68/1.99  fof(f4,axiom,(
% 11.68/1.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f53,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.68/1.99    inference(nnf_transformation,[],[f4])).
% 11.68/1.99  
% 11.68/1.99  fof(f54,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.68/1.99    inference(flattening,[],[f53])).
% 11.68/1.99  
% 11.68/1.99  fof(f71,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.68/1.99    inference(cnf_transformation,[],[f54])).
% 11.68/1.99  
% 11.68/1.99  fof(f108,plain,(
% 11.68/1.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.68/1.99    inference(equality_resolution,[],[f71])).
% 11.68/1.99  
% 11.68/1.99  fof(f5,axiom,(
% 11.68/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f55,plain,(
% 11.68/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.68/1.99    inference(nnf_transformation,[],[f5])).
% 11.68/1.99  
% 11.68/1.99  fof(f72,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f55])).
% 11.68/1.99  
% 11.68/1.99  fof(f15,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f34,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.68/1.99    inference(ennf_transformation,[],[f15])).
% 11.68/1.99  
% 11.68/1.99  fof(f85,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f34])).
% 11.68/1.99  
% 11.68/1.99  fof(f7,axiom,(
% 11.68/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f26,plain,(
% 11.68/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f7])).
% 11.68/1.99  
% 11.68/1.99  fof(f56,plain,(
% 11.68/1.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(nnf_transformation,[],[f26])).
% 11.68/1.99  
% 11.68/1.99  fof(f75,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f56])).
% 11.68/1.99  
% 11.68/1.99  fof(f70,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.68/1.99    inference(cnf_transformation,[],[f54])).
% 11.68/1.99  
% 11.68/1.99  fof(f109,plain,(
% 11.68/1.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.68/1.99    inference(equality_resolution,[],[f70])).
% 11.68/1.99  
% 11.68/1.99  fof(f86,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f34])).
% 11.68/1.99  
% 11.68/1.99  fof(f8,axiom,(
% 11.68/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f27,plain,(
% 11.68/1.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f8])).
% 11.68/1.99  
% 11.68/1.99  fof(f57,plain,(
% 11.68/1.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(nnf_transformation,[],[f27])).
% 11.68/1.99  
% 11.68/1.99  fof(f77,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f57])).
% 11.68/1.99  
% 11.68/1.99  fof(f6,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f25,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f6])).
% 11.68/1.99  
% 11.68/1.99  fof(f74,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f25])).
% 11.68/1.99  
% 11.68/1.99  fof(f73,plain,(
% 11.68/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f55])).
% 11.68/1.99  
% 11.68/1.99  fof(f69,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f54])).
% 11.68/1.99  
% 11.68/1.99  fof(f93,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f58])).
% 11.68/1.99  
% 11.68/1.99  fof(f113,plain,(
% 11.68/1.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 11.68/1.99    inference(equality_resolution,[],[f93])).
% 11.68/1.99  
% 11.68/1.99  fof(f68,plain,(
% 11.68/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f52])).
% 11.68/1.99  
% 11.68/1.99  cnf(c_40,negated_conjecture,
% 11.68/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
% 11.68/1.99      inference(cnf_transformation,[],[f102]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1749,plain,
% 11.68/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_36,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | ~ v1_funct_1(X0)
% 11.68/1.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.68/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1752,plain,
% 11.68/1.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 11.68/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.68/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3471,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0)
% 11.68/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1749,c_1752]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_42,negated_conjecture,
% 11.68/1.99      ( v1_funct_1(sK5) ),
% 11.68/1.99      inference(cnf_transformation,[],[f100]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_45,plain,
% 11.68/1.99      ( v1_funct_1(sK5) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3857,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0) ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_3471,c_45]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_34,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | ~ v1_funct_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1754,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.68/1.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.68/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4506,plain,
% 11.68/1.99      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top
% 11.68/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
% 11.68/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_3857,c_1754]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_47,plain,
% 11.68/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4745,plain,
% 11.68/1.99      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_4506,c_45,c_47]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_22,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | v1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1758,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4754,plain,
% 11.68/1.99      ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4745,c_1758]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_27,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 11.68/1.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.68/1.99      | ~ v1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1755,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6,plain,
% 11.68/1.99      ( r1_tarski(X0,X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f107]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1766,plain,
% 11.68/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_26,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.68/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1756,plain,
% 11.68/1.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 11.68/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4096,plain,
% 11.68/1.99      ( k7_relset_1(sK1,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1749,c_1756]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_38,negated_conjecture,
% 11.68/1.99      ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
% 11.68/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1751,plain,
% 11.68/1.99      ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4181,plain,
% 11.68/1.99      ( r1_tarski(k9_relat_1(sK5,sK2),sK3) = iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_4096,c_1751]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_39,negated_conjecture,
% 11.68/1.99      ( r1_tarski(sK2,sK1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1750,plain,
% 11.68/1.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_25,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1757,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.68/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3486,plain,
% 11.68/1.99      ( k1_relset_1(sK1,sK4,sK5) = k1_relat_1(sK5) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1749,c_1757]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_33,plain,
% 11.68/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.68/1.99      | k1_xboole_0 = X2 ),
% 11.68/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_41,negated_conjecture,
% 11.68/1.99      ( v1_funct_2(sK5,sK1,sK4) ),
% 11.68/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_686,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.68/1.99      | sK5 != X0
% 11.68/1.99      | sK4 != X2
% 11.68/1.99      | sK1 != X1
% 11.68/1.99      | k1_xboole_0 = X2 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_33,c_41]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_687,plain,
% 11.68/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 11.68/1.99      | k1_relset_1(sK1,sK4,sK5) = sK1
% 11.68/1.99      | k1_xboole_0 = sK4 ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_686]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_689,plain,
% 11.68/1.99      ( k1_relset_1(sK1,sK4,sK5) = sK1 | k1_xboole_0 = sK4 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_687,c_40]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3,plain,
% 11.68/1.99      ( v1_xboole_0(k1_xboole_0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_43,negated_conjecture,
% 11.68/1.99      ( ~ v1_xboole_0(sK4) ),
% 11.68/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_536,plain,
% 11.68/1.99      ( sK4 != k1_xboole_0 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_3,c_43]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1030,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1817,plain,
% 11.68/1.99      ( sK4 != X0 | sK4 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1927,plain,
% 11.68/1.99      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1817]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1029,plain,( X0 = X0 ),theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1994,plain,
% 11.68/1.99      ( sK4 = sK4 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1029]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2019,plain,
% 11.68/1.99      ( k1_relset_1(sK1,sK4,sK5) = sK1 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_689,c_536,c_1927,c_1994]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3489,plain,
% 11.68/1.99      ( k1_relat_1(sK5) = sK1 ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_3486,c_2019]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1759,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 11.68/1.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4555,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
% 11.68/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.68/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_3489,c_1759]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2550,plain,
% 11.68/1.99      ( v1_relat_1(sK5) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1749,c_1758]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4635,plain,
% 11.68/1.99      ( r1_tarski(X0,sK1) != iProver_top
% 11.68/1.99      | k1_relat_1(k7_relat_1(sK5,X0)) = X0 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_4555,c_2550]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4636,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
% 11.68/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_4635]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4644,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(sK5,sK2)) = sK2 ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1750,c_4636]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_19,plain,
% 11.68/1.99      ( ~ v1_relat_1(X0)
% 11.68/1.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1761,plain,
% 11.68/1.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2985,plain,
% 11.68/1.99      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2550,c_1761]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4880,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.68/1.99      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 11.68/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1755,c_1757]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_27986,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,k7_relat_1(sK5,X2)) = k1_relat_1(k7_relat_1(sK5,X2))
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,X2),X1) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK5,X2)),X0) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,X2)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2985,c_4880]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_28568,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = k1_relat_1(k7_relat_1(sK5,sK2))
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,X0) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4644,c_27986]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_28591,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,X0) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_28568,c_4644]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_28708,plain,
% 11.68/1.99      ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
% 11.68/1.99      | r1_tarski(sK2,X0) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4181,c_28591]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_28716,plain,
% 11.68/1.99      ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
% 11.68/1.99      | r1_tarski(sK2,X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4754,c_28708]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_28776,plain,
% 11.68/1.99      ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) = sK2 ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1766,c_28716]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31,plain,
% 11.68/1.99      ( v1_funct_2(X0,X1,X2)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | k1_relset_1(X1,X2,X0) != X1
% 11.68/1.99      | k1_xboole_0 = X2 ),
% 11.68/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_37,negated_conjecture,
% 11.68/1.99      ( ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
% 11.68/1.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.68/1.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_670,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.68/1.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 11.68/1.99      | k1_relset_1(X1,X2,X0) != X1
% 11.68/1.99      | sK3 != X2
% 11.68/1.99      | sK2 != X1
% 11.68/1.99      | k1_xboole_0 = X2 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_31,c_37]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_671,plain,
% 11.68/1.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.68/1.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 11.68/1.99      | k1_xboole_0 = sK3 ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_670]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1741,plain,
% 11.68/1.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 11.68/1.99      | k1_xboole_0 = sK3
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.68/1.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_672,plain,
% 11.68/1.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 11.68/1.99      | k1_xboole_0 = sK3
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.68/1.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_35,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | ~ v1_funct_1(X0)
% 11.68/1.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1830,plain,
% 11.68/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 11.68/1.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | ~ v1_funct_1(sK5) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_35]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1831,plain,
% 11.68/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
% 11.68/1.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
% 11.68/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2081,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.68/1.99      | k1_xboole_0 = sK3
% 11.68/1.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_1741,c_45,c_47,c_672,c_1831]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2082,plain,
% 11.68/1.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 11.68/1.99      | k1_xboole_0 = sK3
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_2081]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3863,plain,
% 11.68/1.99      ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) != sK2
% 11.68/1.99      | sK3 = k1_xboole_0
% 11.68/1.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_3857,c_2082]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31660,plain,
% 11.68/1.99      ( sK3 = k1_xboole_0
% 11.68/1.99      | sK2 != sK2
% 11.68/1.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_28776,c_3863]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31756,plain,
% 11.68/1.99      ( sK3 = k1_xboole_0
% 11.68/1.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 11.68/1.99      inference(equality_resolution_simp,[status(thm)],[c_31660]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31759,plain,
% 11.68/1.99      ( sK3 = k1_xboole_0
% 11.68/1.99      | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1755,c_31756]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31760,plain,
% 11.68/1.99      ( sK3 = k1_xboole_0
% 11.68/1.99      | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK2) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_31759,c_4644]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31761,plain,
% 11.68/1.99      ( sK3 = k1_xboole_0
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,sK2),sK3) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK2) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_31760,c_2985]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_0,plain,
% 11.68/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2189,plain,
% 11.68/1.99      ( ~ r2_hidden(sK0(X0,sK2),sK2) | r1_tarski(X0,sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10630,plain,
% 11.68/1.99      ( ~ r2_hidden(sK0(sK2,sK2),sK2) | r1_tarski(sK2,sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2189]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10633,plain,
% 11.68/1.99      ( r2_hidden(sK0(sK2,sK2),sK2) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK2) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_10630]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1,plain,
% 11.68/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2190,plain,
% 11.68/1.99      ( r2_hidden(sK0(X0,sK2),X0) | r1_tarski(X0,sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10628,plain,
% 11.68/1.99      ( r2_hidden(sK0(sK2,sK2),sK2) | r1_tarski(sK2,sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2190]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10637,plain,
% 11.68/1.99      ( r2_hidden(sK0(sK2,sK2),sK2) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK2) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_10628]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31849,plain,
% 11.68/1.99      ( sK3 = k1_xboole_0
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_31761,c_4181,c_10633,c_10637]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_31854,plain,
% 11.68/1.99      ( sK3 = k1_xboole_0 ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4754,c_31849]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_32001,plain,
% 11.68/1.99      ( r1_tarski(k9_relat_1(sK5,sK2),k1_xboole_0) = iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_31854,c_4181]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7,plain,
% 11.68/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f108]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_11,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1764,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.68/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4874,plain,
% 11.68/1.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1755,c_1764]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24661,plain,
% 11.68/1.99      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_7,c_4874]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24,plain,
% 11.68/1.99      ( v4_relat_1(X0,X1)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.68/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14,plain,
% 11.68/1.99      ( ~ v4_relat_1(X0,X1)
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1)
% 11.68/1.99      | ~ v1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_556,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1)
% 11.68/1.99      | ~ v1_relat_1(X0) ),
% 11.68/1.99      inference(resolution,[status(thm)],[c_24,c_14]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_560,plain,
% 11.68/1.99      ( r1_tarski(k1_relat_1(X0),X1)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_556,c_22]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_561,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_560]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1746,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2918,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_7,c_1746]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4872,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_7,c_1755]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_5006,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1766,c_4872]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24678,plain,
% 11.68/1.99      ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_24661,c_2918,c_5006]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24679,plain,
% 11.68/1.99      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_24678]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24690,plain,
% 11.68/1.99      ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2985,c_24679]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_25090,plain,
% 11.68/1.99      ( r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_24690,c_4754]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_25091,plain,
% 11.68/1.99      ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_25090]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_32093,plain,
% 11.68/1.99      ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_32001,c_25091]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8,plain,
% 11.68/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4873,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 11.68/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_8,c_1755]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_5341,plain,
% 11.68/1.99      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2985,c_4873]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6931,plain,
% 11.68/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
% 11.68/1.99      | m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_5341,c_4754]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6932,plain,
% 11.68/1.99      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_6931]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6940,plain,
% 11.68/1.99      ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(k9_relat_1(sK5,sK2),X0) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4644,c_6932]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6962,plain,
% 11.68/1.99      ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1766,c_6940]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23,plain,
% 11.68/1.99      ( v5_relat_1(X0,X1)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.68/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_16,plain,
% 11.68/1.99      ( ~ v5_relat_1(X0,X1)
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X1)
% 11.68/1.99      | ~ v1_relat_1(X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_577,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X2)
% 11.68/1.99      | ~ v1_relat_1(X0) ),
% 11.68/1.99      inference(resolution,[status(thm)],[c_23,c_16]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_581,plain,
% 11.68/1.99      ( r1_tarski(k2_relat_1(X0),X2)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_577,c_22]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_582,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_581]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1745,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2470,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.68/1.99      | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_8,c_1745]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7460,plain,
% 11.68/1.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),X0) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_6962,c_2470]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7470,plain,
% 11.68/1.99      ( r1_tarski(k9_relat_1(sK5,sK2),X0) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_7460,c_2985]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1769,plain,
% 11.68/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.68/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_12,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.68/1.99      | ~ r2_hidden(X2,X0)
% 11.68/1.99      | ~ v1_xboole_0(X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_322,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.68/1.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_323,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_322]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_396,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 11.68/1.99      inference(bin_hyper_res,[status(thm)],[c_12,c_323]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_540,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_3,c_396]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_541,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_540]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1747,plain,
% 11.68/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.68/1.99      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2539,plain,
% 11.68/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.68/1.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1769,c_1747]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2605,plain,
% 11.68/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1766,c_2539]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4645,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = k1_xboole_0 ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2605,c_4636]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4815,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),X0)) = X0
% 11.68/1.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 11.68/1.99      | v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4645,c_1759]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4770,plain,
% 11.68/1.99      ( v1_relat_1(k7_relat_1(sK5,k1_xboole_0)) = iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_4754]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23928,plain,
% 11.68/1.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 11.68/1.99      | k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),X0)) = X0 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_4815,c_4770]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23929,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),X0)) = X0
% 11.68/1.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_23928]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23944,plain,
% 11.68/1.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK5,k1_xboole_0),k9_relat_1(sK5,sK2))) = k9_relat_1(sK5,sK2)
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_7470,c_23929]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_9,plain,
% 11.68/1.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.68/1.99      | k1_xboole_0 = X1
% 11.68/1.99      | k1_xboole_0 = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_132,plain,
% 11.68/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.68/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_133,plain,
% 11.68/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_135,plain,
% 11.68/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_134,plain,
% 11.68/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_136,plain,
% 11.68/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_134]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1901,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.68/1.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1902,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_1901]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1970,plain,
% 11.68/1.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1974,plain,
% 11.68/1.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_1970]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_30,plain,
% 11.68/1.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 11.68/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.68/1.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f113]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_638,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.68/1.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.68/1.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 11.68/1.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 11.68/1.99      | sK3 != X1
% 11.68/1.99      | sK2 != k1_xboole_0 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_639,plain,
% 11.68/1.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.68/1.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 11.68/1.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 11.68/1.99      | sK2 != k1_xboole_0 ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_638]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1743,plain,
% 11.68/1.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 11.68/1.99      | sK2 != k1_xboole_0
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 11.68/1.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1773,plain,
% 11.68/1.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 11.68/1.99      | sK2 != k1_xboole_0
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.68/1.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 11.68/1.99      inference(demodulation,[status(thm)],[c_1743,c_8]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2334,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.68/1.99      | sK2 != k1_xboole_0
% 11.68/1.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_1773,c_45,c_47,c_1831]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2335,plain,
% 11.68/1.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 11.68/1.99      | sK2 != k1_xboole_0
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_2334]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2348,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 11.68/1.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2814,plain,
% 11.68/1.99      ( r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)))
% 11.68/1.99      | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2190]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2821,plain,
% 11.68/1.99      ( r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) = iProver_top
% 11.68/1.99      | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_2814]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2849,plain,
% 11.68/1.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3013,plain,
% 11.68/1.99      ( r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2)
% 11.68/1.99      | r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3017,plain,
% 11.68/1.99      ( r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_3013]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1936,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3058,plain,
% 11.68/1.99      ( ~ r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2)
% 11.68/1.99      | ~ r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)))
% 11.68/1.99      | sK2 = k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1936]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3059,plain,
% 11.68/1.99      ( sK2 = k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_3058]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2972,plain,
% 11.68/1.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != X0
% 11.68/1.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
% 11.68/1.99      | k1_xboole_0 != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4088,plain,
% 11.68/1.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
% 11.68/1.99      | k1_xboole_0 != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2972]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4145,plain,
% 11.68/1.99      ( ~ r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)))
% 11.68/1.99      | ~ r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_541]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4146,plain,
% 11.68/1.99      ( r2_hidden(sK0(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),sK2),k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_4145]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3748,plain,
% 11.68/1.99      ( X0 != X1
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X1
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) = X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6417,plain,
% 11.68/1.99      ( X0 != k7_relat_1(sK5,sK2)
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) = X0
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_3748]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6418,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) = k1_xboole_0
% 11.68/1.99      | k1_xboole_0 != k7_relat_1(sK5,sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_6417]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1765,plain,
% 11.68/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.68/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3032,plain,
% 11.68/1.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1765,c_2918]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1767,plain,
% 11.68/1.99      ( X0 = X1
% 11.68/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.68/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3784,plain,
% 11.68/1.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2605,c_1767]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6568,plain,
% 11.68/1.99      ( k1_relat_1(X0) = k1_xboole_0
% 11.68/1.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_3032,c_3784]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6615,plain,
% 11.68/1.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 11.68/1.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_6568]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1825,plain,
% 11.68/1.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6991,plain,
% 11.68/1.99      ( sK2 != k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | sK2 = k1_xboole_0
% 11.68/1.99      | k1_xboole_0 != k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1825]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7104,plain,
% 11.68/1.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 11.68/1.99      | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_561]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7105,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_7104]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7107,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) = iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_7105]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4400,plain,
% 11.68/1.99      ( k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) != X0
% 11.68/1.99      | k1_xboole_0 != X0
% 11.68/1.99      | k1_xboole_0 = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7577,plain,
% 11.68/1.99      ( k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(X0)
% 11.68/1.99      | k1_xboole_0 != k1_relat_1(X0)
% 11.68/1.99      | k1_xboole_0 = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_4400]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7578,plain,
% 11.68/1.99      ( k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k1_xboole_0)
% 11.68/1.99      | k1_xboole_0 = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_7577]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7731,plain,
% 11.68/1.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 11.68/1.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_25]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8147,plain,
% 11.68/1.99      ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_541]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8148,plain,
% 11.68/1.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_8147]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8211,plain,
% 11.68/1.99      ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_541]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2061,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,sK2) | ~ r1_tarski(sK2,k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_541]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8401,plain,
% 11.68/1.99      ( ~ r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2)
% 11.68/1.99      | ~ r1_tarski(sK2,k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2061]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8402,plain,
% 11.68/1.99      ( r2_hidden(sK0(sK2,k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))),sK2) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_8401]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8982,plain,
% 11.68/1.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 11.68/1.99      | ~ v1_funct_1(sK5)
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) = k7_relat_1(sK5,sK2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_36]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_9050,plain,
% 11.68/1.99      ( k1_relat_1(X0) != X1
% 11.68/1.99      | k1_xboole_0 != X1
% 11.68/1.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_9051,plain,
% 11.68/1.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 11.68/1.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 11.68/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_9050]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7458,plain,
% 11.68/1.99      ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_6962,c_1764]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_9129,plain,
% 11.68/1.99      ( k7_relat_1(sK5,sK2) = k1_xboole_0
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_7458,c_3784]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1031,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.68/1.99      theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14265,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1)
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X2)
% 11.68/1.99      | X2 != X1
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1031]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14267,plain,
% 11.68/1.99      ( r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0)
% 11.68/1.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 11.68/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_14265]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14266,plain,
% 11.68/1.99      ( X0 != X1
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X2
% 11.68/1.99      | r1_tarski(X2,X1) != iProver_top
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_14265]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14268,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 11.68/1.99      | k1_xboole_0 != k1_xboole_0
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) = iProver_top
% 11.68/1.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_14266]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18113,plain,
% 11.68/1.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.68/1.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_25]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4590,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,X2) != X3
% 11.68/1.99      | k1_xboole_0 != X3
% 11.68/1.99      | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_11494,plain,
% 11.68/1.99      ( k1_relset_1(X0,X1,X2) != k1_relat_1(X2)
% 11.68/1.99      | k1_xboole_0 = k1_relset_1(X0,X1,X2)
% 11.68/1.99      | k1_xboole_0 != k1_relat_1(X2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_4590]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18167,plain,
% 11.68/1.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k1_xboole_0 = k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k1_xboole_0 != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_11494]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1036,plain,
% 11.68/1.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 11.68/1.99      theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18617,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 11.68/1.99      | k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(X0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1036]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18618,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 11.68/1.99      | k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relat_1(k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_18617]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4292,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1)
% 11.68/1.99      | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),X2)
% 11.68/1.99      | X2 != X1
% 11.68/1.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1031]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_20048,plain,
% 11.68/1.99      ( r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),X0)
% 11.68/1.99      | ~ r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),X1)
% 11.68/1.99      | X0 != X1
% 11.68/1.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_4292]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_20049,plain,
% 11.68/1.99      ( X0 != X1
% 11.68/1.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),X0) = iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_20048]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_20051,plain,
% 11.68/1.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 11.68/1.99      | k1_xboole_0 != k1_xboole_0
% 11.68/1.99      | r1_tarski(k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) = iProver_top
% 11.68/1.99      | r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_20049]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21318,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(X0))
% 11.68/1.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21319,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(X0)) = iProver_top
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_21318]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21321,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.68/1.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_21319]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1034,plain,
% 11.68/1.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.68/1.99      theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21332,plain,
% 11.68/1.99      ( k2_zfmisc_1(X0,X1) != X2
% 11.68/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1034]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21333,plain,
% 11.68/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.68/1.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_21332]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23858,plain,
% 11.68/1.99      ( X0 != X1 | X0 = k7_relat_1(sK5,sK2) | k7_relat_1(sK5,sK2) != X1 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23859,plain,
% 11.68/1.99      ( k7_relat_1(sK5,sK2) != k1_xboole_0
% 11.68/1.99      | k1_xboole_0 = k7_relat_1(sK5,sK2)
% 11.68/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_23858]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1035,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.68/1.99      theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2429,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,X1)
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 11.68/1.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != X1 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1035]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3738,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.68/1.99      | ~ m1_subset_1(k7_relat_1(sK5,sK2),X2)
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
% 11.68/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != X2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2429]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23872,plain,
% 11.68/1.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.68/1.99      | ~ m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X2))
% 11.68/1.99      | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
% 11.68/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_3738]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23873,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
% 11.68/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2)
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 11.68/1.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X2)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_23872]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23875,plain,
% 11.68/1.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2)
% 11.68/1.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 11.68/1.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 11.68/1.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_23873]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24520,plain,
% 11.68/1.99      ( r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_23944,c_42,c_40,c_132,c_133,c_135,c_136,c_1901,c_1902,
% 11.68/1.99                 c_1970,c_1974,c_2335,c_2348,c_2821,c_2849,c_3017,c_3059,
% 11.68/1.99                 c_4088,c_4146,c_6418,c_6615,c_6962,c_6991,c_7107,c_7578,
% 11.68/1.99                 c_7731,c_8147,c_8148,c_8211,c_8402,c_8982,c_9051,c_9129,
% 11.68/1.99                 c_14267,c_14268,c_18113,c_18167,c_18618,c_20051,c_21321,
% 11.68/1.99                 c_21333,c_23859,c_23875]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6555,plain,
% 11.68/1.99      ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,X0) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_4644,c_3032]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6579,plain,
% 11.68/1.99      ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_6555]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(contradiction,plain,
% 11.68/1.99      ( $false ),
% 11.68/1.99      inference(minisat,[status(thm)],[c_32093,c_24520,c_6579]) ).
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  ------                               Statistics
% 11.68/1.99  
% 11.68/1.99  ------ General
% 11.68/1.99  
% 11.68/1.99  abstr_ref_over_cycles:                  0
% 11.68/1.99  abstr_ref_under_cycles:                 0
% 11.68/1.99  gc_basic_clause_elim:                   0
% 11.68/1.99  forced_gc_time:                         0
% 11.68/1.99  parsing_time:                           0.009
% 11.68/1.99  unif_index_cands_time:                  0.
% 11.68/1.99  unif_index_add_time:                    0.
% 11.68/1.99  orderings_time:                         0.
% 11.68/1.99  out_proof_time:                         0.024
% 11.68/1.99  total_time:                             1.02
% 11.68/1.99  num_of_symbols:                         56
% 11.68/1.99  num_of_terms:                           37022
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing
% 11.68/1.99  
% 11.68/1.99  num_of_splits:                          0
% 11.68/1.99  num_of_split_atoms:                     0
% 11.68/1.99  num_of_reused_defs:                     0
% 11.68/1.99  num_eq_ax_congr_red:                    27
% 11.68/1.99  num_of_sem_filtered_clauses:            1
% 11.68/1.99  num_of_subtypes:                        0
% 11.68/1.99  monotx_restored_types:                  0
% 11.68/1.99  sat_num_of_epr_types:                   0
% 11.68/1.99  sat_num_of_non_cyclic_types:            0
% 11.68/1.99  sat_guarded_non_collapsed_types:        0
% 11.68/1.99  num_pure_diseq_elim:                    0
% 11.68/1.99  simp_replaced_by:                       0
% 11.68/1.99  res_preprocessed:                       180
% 11.68/1.99  prep_upred:                             0
% 11.68/1.99  prep_unflattend:                        34
% 11.68/1.99  smt_new_axioms:                         0
% 11.68/1.99  pred_elim_cands:                        5
% 11.68/1.99  pred_elim:                              4
% 11.68/1.99  pred_elim_cl:                           7
% 11.68/1.99  pred_elim_cycles:                       6
% 11.68/1.99  merged_defs:                            8
% 11.68/1.99  merged_defs_ncl:                        0
% 11.68/1.99  bin_hyper_res:                          9
% 11.68/1.99  prep_cycles:                            4
% 11.68/1.99  pred_elim_time:                         0.006
% 11.68/1.99  splitting_time:                         0.
% 11.68/1.99  sem_filter_time:                        0.
% 11.68/1.99  monotx_time:                            0.002
% 11.68/1.99  subtype_inf_time:                       0.
% 11.68/1.99  
% 11.68/1.99  ------ Problem properties
% 11.68/1.99  
% 11.68/1.99  clauses:                                36
% 11.68/1.99  conjectures:                            4
% 11.68/1.99  epr:                                    7
% 11.68/1.99  horn:                                   33
% 11.68/1.99  ground:                                 11
% 11.68/1.99  unary:                                  9
% 11.68/1.99  binary:                                 14
% 11.68/1.99  lits:                                   85
% 11.68/1.99  lits_eq:                                26
% 11.68/1.99  fd_pure:                                0
% 11.68/1.99  fd_pseudo:                              0
% 11.68/1.99  fd_cond:                                1
% 11.68/1.99  fd_pseudo_cond:                         1
% 11.68/1.99  ac_symbols:                             0
% 11.68/1.99  
% 11.68/1.99  ------ Propositional Solver
% 11.68/1.99  
% 11.68/1.99  prop_solver_calls:                      34
% 11.68/1.99  prop_fast_solver_calls:                 2258
% 11.68/1.99  smt_solver_calls:                       0
% 11.68/1.99  smt_fast_solver_calls:                  0
% 11.68/1.99  prop_num_of_clauses:                    15246
% 11.68/1.99  prop_preprocess_simplified:             26011
% 11.68/1.99  prop_fo_subsumed:                       81
% 11.68/1.99  prop_solver_time:                       0.
% 11.68/1.99  smt_solver_time:                        0.
% 11.68/1.99  smt_fast_solver_time:                   0.
% 11.68/1.99  prop_fast_solver_time:                  0.
% 11.68/1.99  prop_unsat_core_time:                   0.001
% 11.68/1.99  
% 11.68/1.99  ------ QBF
% 11.68/1.99  
% 11.68/1.99  qbf_q_res:                              0
% 11.68/1.99  qbf_num_tautologies:                    0
% 11.68/1.99  qbf_prep_cycles:                        0
% 11.68/1.99  
% 11.68/1.99  ------ BMC1
% 11.68/1.99  
% 11.68/1.99  bmc1_current_bound:                     -1
% 11.68/1.99  bmc1_last_solved_bound:                 -1
% 11.68/1.99  bmc1_unsat_core_size:                   -1
% 11.68/1.99  bmc1_unsat_core_parents_size:           -1
% 11.68/1.99  bmc1_merge_next_fun:                    0
% 11.68/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation
% 11.68/1.99  
% 11.68/1.99  inst_num_of_clauses:                    3991
% 11.68/1.99  inst_num_in_passive:                    2117
% 11.68/1.99  inst_num_in_active:                     1805
% 11.68/1.99  inst_num_in_unprocessed:                69
% 11.68/1.99  inst_num_of_loops:                      2500
% 11.68/1.99  inst_num_of_learning_restarts:          0
% 11.68/1.99  inst_num_moves_active_passive:          691
% 11.68/1.99  inst_lit_activity:                      0
% 11.68/1.99  inst_lit_activity_moves:                0
% 11.68/1.99  inst_num_tautologies:                   0
% 11.68/1.99  inst_num_prop_implied:                  0
% 11.68/1.99  inst_num_existing_simplified:           0
% 11.68/1.99  inst_num_eq_res_simplified:             0
% 11.68/1.99  inst_num_child_elim:                    0
% 11.68/1.99  inst_num_of_dismatching_blockings:      1502
% 11.68/1.99  inst_num_of_non_proper_insts:           4893
% 11.68/1.99  inst_num_of_duplicates:                 0
% 11.68/1.99  inst_inst_num_from_inst_to_res:         0
% 11.68/1.99  inst_dismatching_checking_time:         0.
% 11.68/1.99  
% 11.68/1.99  ------ Resolution
% 11.68/1.99  
% 11.68/1.99  res_num_of_clauses:                     0
% 11.68/1.99  res_num_in_passive:                     0
% 11.68/1.99  res_num_in_active:                      0
% 11.68/1.99  res_num_of_loops:                       184
% 11.68/1.99  res_forward_subset_subsumed:            155
% 11.68/1.99  res_backward_subset_subsumed:           0
% 11.68/1.99  res_forward_subsumed:                   0
% 11.68/1.99  res_backward_subsumed:                  0
% 11.68/1.99  res_forward_subsumption_resolution:     0
% 11.68/1.99  res_backward_subsumption_resolution:    0
% 11.68/1.99  res_clause_to_clause_subsumption:       6137
% 11.68/1.99  res_orphan_elimination:                 0
% 11.68/1.99  res_tautology_del:                      329
% 11.68/1.99  res_num_eq_res_simplified:              0
% 11.68/1.99  res_num_sel_changes:                    0
% 11.68/1.99  res_moves_from_active_to_pass:          0
% 11.68/1.99  
% 11.68/1.99  ------ Superposition
% 11.68/1.99  
% 11.68/1.99  sup_time_total:                         0.
% 11.68/1.99  sup_time_generating:                    0.
% 11.68/1.99  sup_time_sim_full:                      0.
% 11.68/1.99  sup_time_sim_immed:                     0.
% 11.68/1.99  
% 11.68/1.99  sup_num_of_clauses:                     1610
% 11.68/1.99  sup_num_in_active:                      324
% 11.68/1.99  sup_num_in_passive:                     1286
% 11.68/1.99  sup_num_of_loops:                       499
% 11.68/1.99  sup_fw_superposition:                   1748
% 11.68/1.99  sup_bw_superposition:                   882
% 11.68/1.99  sup_immediate_simplified:               751
% 11.68/1.99  sup_given_eliminated:                   7
% 11.68/1.99  comparisons_done:                       0
% 11.68/1.99  comparisons_avoided:                    0
% 11.68/1.99  
% 11.68/1.99  ------ Simplifications
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  sim_fw_subset_subsumed:                 123
% 11.68/1.99  sim_bw_subset_subsumed:                 72
% 11.68/1.99  sim_fw_subsumed:                        114
% 11.68/1.99  sim_bw_subsumed:                        126
% 11.68/1.99  sim_fw_subsumption_res:                 0
% 11.68/1.99  sim_bw_subsumption_res:                 0
% 11.68/1.99  sim_tautology_del:                      16
% 11.68/1.99  sim_eq_tautology_del:                   163
% 11.68/1.99  sim_eq_res_simp:                        2
% 11.68/1.99  sim_fw_demodulated:                     210
% 11.68/1.99  sim_bw_demodulated:                     33
% 11.68/1.99  sim_light_normalised:                   353
% 11.68/1.99  sim_joinable_taut:                      0
% 11.68/1.99  sim_joinable_simp:                      0
% 11.68/1.99  sim_ac_normalised:                      0
% 11.68/1.99  sim_smt_subsumption:                    0
% 11.68/1.99  
%------------------------------------------------------------------------------
