%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:57 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 849 expanded)
%              Number of clauses        :   99 ( 265 expanded)
%              Number of leaves         :   25 ( 207 expanded)
%              Depth                    :   21
%              Number of atoms          :  658 (5220 expanded)
%              Number of equality atoms :  201 ( 416 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f96])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK6,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK6),k6_partfun1(X0))
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK6,X1,X0)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK3)
            | ~ v2_funct_1(sK5) )
          & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,X3),k6_partfun1(sK3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
          & v1_funct_2(X3,sK4,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ~ v2_funct_2(sK6,sK3)
      | ~ v2_funct_1(sK5) )
    & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    & v1_funct_2(sK6,sK4,sK3)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f47,f62,f61])).

fof(f106,plain,(
    r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f63])).

fof(f103,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f105,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f63])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f104,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f114,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f92])).

fof(f107,plain,
    ( ~ v2_funct_2(sK6,sK3)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f84,f96])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f56,f57])).

fof(f81,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1838,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1834,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1835,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3431,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1835])).

cnf(c_3730,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1834,c_3431])).

cnf(c_3739,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1838,c_3730])).

cnf(c_31,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1820,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3903,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3739,c_1820])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_10])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_462,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_21])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_1811,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_3947,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3739,c_1811])).

cnf(c_6962,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3903,c_3947])).

cnf(c_14,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6964,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6962,c_14])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1822,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) != X0
    | k6_partfun1(sK3) != X3
    | sK3 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_581,plain,
    ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ m1_subset_1(k6_partfun1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_589,plain,
    ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_581,c_31])).

cnf(c_1807,plain,
    ( k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_5419,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_1807])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_46,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_48,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5596,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5419,c_43,c_45,c_46,c_48])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1818,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5622,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(k6_partfun1(sK3)) != iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5596,c_1818])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_44,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_47,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1817,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1823,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4040,plain,
    ( k2_relset_1(sK4,sK3,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1817,c_1823])).

cnf(c_32,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_593,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_594,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | ~ v1_funct_2(X2,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X1,sK3,X0) = sK3
    | k6_partfun1(sK3) != k6_partfun1(sK3) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_834,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | ~ v1_funct_2(X2,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X1,sK3,X0) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_594])).

cnf(c_1806,plain,
    ( k1_partfun1(sK3,X0,X0,sK3,X1,X2) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X0,sK3,X2) = sK3
    | v1_funct_2(X2,X0,sK3) != iProver_top
    | v1_funct_2(X1,sK3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_2606,plain,
    ( k2_relset_1(sK4,sK3,sK6) = sK3
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1806])).

cnf(c_2609,plain,
    ( k2_relset_1(sK4,sK3,sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2606,c_43,c_44,c_45,c_46,c_47,c_48])).

cnf(c_4050,plain,
    ( k2_relat_1(sK6) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4040,c_2609])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_498,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_499,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_509,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_499,c_21])).

cnf(c_35,negated_conjecture,
    ( ~ v2_funct_2(sK6,sK3)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK5)
    | k2_relat_1(X0) != sK3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_509,c_35])).

cnf(c_525,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6))))
    | ~ v2_funct_1(sK5)
    | k2_relat_1(sK6) != sK3 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_1171,plain,
    ( ~ v2_funct_1(sK5)
    | sP0_iProver_split
    | k2_relat_1(sK6) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_525])).

cnf(c_1809,plain,
    ( k2_relat_1(sK6) != sK3
    | v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_4240,plain,
    ( sK3 != sK3
    | v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_4050,c_1809])).

cnf(c_4241,plain,
    ( v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4240])).

cnf(c_1170,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_525])).

cnf(c_1810,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_4239,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_4050,c_1810])).

cnf(c_4487,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_4239])).

cnf(c_5731,plain,
    ( v2_funct_1(k6_partfun1(sK3)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5622,c_43,c_44,c_45,c_46,c_47,c_48,c_4241,c_4487])).

cnf(c_5732,plain,
    ( sK3 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5731])).

cnf(c_20,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1825,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5737,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5732,c_1825])).

cnf(c_1814,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3946,plain,
    ( r1_tarski(k1_relat_1(sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1811])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1837,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4207,plain,
    ( k1_relat_1(sK5) = sK3
    | r1_tarski(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_1837])).

cnf(c_5747,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5737,c_4207])).

cnf(c_2164,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2195,plain,
    ( r2_hidden(sK2(sK5),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | v2_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4253,plain,
    ( ~ v2_funct_1(sK5)
    | sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4241])).

cnf(c_1175,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4264,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK5))
    | k1_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_4266,plain,
    ( v1_xboole_0(k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4264])).

cnf(c_4488,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4487])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4789,plain,
    ( ~ r2_hidden(sK2(sK5),k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6769,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5747,c_42,c_40,c_2,c_2164,c_2195,c_4253,c_4266,c_4488,c_4789])).

cnf(c_6975,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_6964,c_6769])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:14:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
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
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 37
% 3.45/0.99  conjectures                             6
% 3.45/0.99  EPR                                     9
% 3.45/0.99  Horn                                    32
% 3.45/0.99  unary                                   12
% 3.45/0.99  binary                                  8
% 3.45/0.99  lits                                    112
% 3.45/0.99  lits eq                                 20
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 3
% 3.45/0.99  fd_pseudo_cond                          3
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
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    v1_xboole_0(k1_xboole_0)),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f66,plain,(
% 3.45/0.99    v1_xboole_0(k1_xboole_0)),
% 3.45/0.99    inference(cnf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,axiom,(
% 3.45/0.99    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f26,plain,(
% 3.45/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f71,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f25,plain,(
% 3.45/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.45/0.99    inference(ennf_transformation,[],[f4])).
% 3.45/0.99  
% 3.45/0.99  fof(f70,plain,(
% 3.45/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f18,axiom,(
% 3.45/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f24,plain,(
% 3.45/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.45/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f95,plain,(
% 3.45/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f24])).
% 3.45/0.99  
% 3.45/0.99  fof(f13,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f34,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f13])).
% 3.45/0.99  
% 3.45/0.99  fof(f86,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f34])).
% 3.45/0.99  
% 3.45/0.99  fof(f7,axiom,(
% 3.45/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f28,plain,(
% 3.45/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f7])).
% 3.45/0.99  
% 3.45/0.99  fof(f54,plain,(
% 3.45/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(nnf_transformation,[],[f28])).
% 3.45/0.99  
% 3.45/0.99  fof(f73,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f54])).
% 3.45/0.99  
% 3.45/0.99  fof(f12,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f85,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f9,axiom,(
% 3.45/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f77,plain,(
% 3.45/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.45/0.99    inference(cnf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f19,axiom,(
% 3.45/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f96,plain,(
% 3.45/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f109,plain,(
% 3.45/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.45/0.99    inference(definition_unfolding,[],[f77,f96])).
% 3.45/0.99  
% 3.45/0.99  fof(f17,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f40,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.45/0.99    inference(ennf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f41,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.45/0.99    inference(flattening,[],[f40])).
% 3.45/0.99  
% 3.45/0.99  fof(f94,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f41])).
% 3.45/0.99  
% 3.45/0.99  fof(f15,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f36,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.45/0.99    inference(ennf_transformation,[],[f15])).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(flattening,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f59,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(nnf_transformation,[],[f37])).
% 3.45/0.99  
% 3.45/0.99  fof(f89,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f59])).
% 3.45/0.99  
% 3.45/0.99  fof(f22,conjecture,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f23,negated_conjecture,(
% 3.45/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.45/0.99    inference(negated_conjecture,[],[f22])).
% 3.45/0.99  
% 3.45/0.99  fof(f46,plain,(
% 3.45/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.45/0.99    inference(ennf_transformation,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f47,plain,(
% 3.45/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.45/0.99    inference(flattening,[],[f46])).
% 3.45/0.99  
% 3.45/0.99  fof(f62,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK6,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK6),k6_partfun1(X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK6,X1,X0) & v1_funct_1(sK6))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f61,plain,(
% 3.45/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK3) | ~v2_funct_1(sK5)) & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,X3),k6_partfun1(sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(X3,sK4,sK3) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f63,plain,(
% 3.45/0.99    ((~v2_funct_2(sK6,sK3) | ~v2_funct_1(sK5)) & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f47,f62,f61])).
% 3.45/0.99  
% 3.45/0.99  fof(f106,plain,(
% 3.45/0.99    r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3))),
% 3.45/0.99    inference(cnf_transformation,[],[f63])).
% 3.45/0.99  
% 3.45/0.99  fof(f100,plain,(
% 3.45/0.99    v1_funct_1(sK5)),
% 3.45/0.99    inference(cnf_transformation,[],[f63])).
% 3.45/0.99  
% 3.45/0.99  fof(f102,plain,(
% 3.45/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.45/0.99    inference(cnf_transformation,[],[f63])).
% 3.45/0.99  
% 3.45/0.99  fof(f103,plain,(
% 3.45/0.99    v1_funct_1(sK6)),
% 3.45/0.99    inference(cnf_transformation,[],[f63])).
% 3.45/0.99  
% 3.45/0.99  fof(f105,plain,(
% 3.45/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 3.45/0.99    inference(cnf_transformation,[],[f63])).
% 3.45/0.99  
% 3.45/0.99  fof(f21,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f44,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.45/1.00    inference(ennf_transformation,[],[f21])).
% 3.45/1.00  
% 3.45/1.00  fof(f45,plain,(
% 3.45/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.45/1.00    inference(flattening,[],[f44])).
% 3.45/1.00  
% 3.45/1.00  fof(f98,plain,(
% 3.45/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f45])).
% 3.45/1.00  
% 3.45/1.00  fof(f101,plain,(
% 3.45/1.00    v1_funct_2(sK5,sK3,sK4)),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f104,plain,(
% 3.45/1.00    v1_funct_2(sK6,sK4,sK3)),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f14,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f35,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f14])).
% 3.45/1.00  
% 3.45/1.00  fof(f88,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f35])).
% 3.45/1.00  
% 3.45/1.00  fof(f20,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f42,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.45/1.00    inference(ennf_transformation,[],[f20])).
% 3.45/1.00  
% 3.45/1.00  fof(f43,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.45/1.00    inference(flattening,[],[f42])).
% 3.45/1.00  
% 3.45/1.00  fof(f97,plain,(
% 3.45/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f43])).
% 3.45/1.00  
% 3.45/1.00  fof(f87,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f34])).
% 3.45/1.00  
% 3.45/1.00  fof(f16,axiom,(
% 3.45/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f38,plain,(
% 3.45/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.45/1.00    inference(ennf_transformation,[],[f16])).
% 3.45/1.00  
% 3.45/1.00  fof(f39,plain,(
% 3.45/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(flattening,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f60,plain,(
% 3.45/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(nnf_transformation,[],[f39])).
% 3.45/1.00  
% 3.45/1.00  fof(f92,plain,(
% 3.45/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f60])).
% 3.45/1.00  
% 3.45/1.00  fof(f114,plain,(
% 3.45/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(equality_resolution,[],[f92])).
% 3.45/1.00  
% 3.45/1.00  fof(f107,plain,(
% 3.45/1.00    ~v2_funct_2(sK6,sK3) | ~v2_funct_1(sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f11,axiom,(
% 3.45/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f84,plain,(
% 3.45/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f11])).
% 3.45/1.00  
% 3.45/1.00  fof(f110,plain,(
% 3.45/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.45/1.00    inference(definition_unfolding,[],[f84,f96])).
% 3.45/1.00  
% 3.45/1.00  fof(f3,axiom,(
% 3.45/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f52,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(nnf_transformation,[],[f3])).
% 3.45/1.00  
% 3.45/1.00  fof(f53,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(flattening,[],[f52])).
% 3.45/1.00  
% 3.45/1.00  fof(f69,plain,(
% 3.45/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f53])).
% 3.45/1.00  
% 3.45/1.00  fof(f10,axiom,(
% 3.45/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f31,plain,(
% 3.45/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.45/1.00    inference(ennf_transformation,[],[f10])).
% 3.45/1.00  
% 3.45/1.00  fof(f32,plain,(
% 3.45/1.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/1.00    inference(flattening,[],[f31])).
% 3.45/1.00  
% 3.45/1.00  fof(f55,plain,(
% 3.45/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/1.00    inference(nnf_transformation,[],[f32])).
% 3.45/1.00  
% 3.45/1.00  fof(f56,plain,(
% 3.45/1.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/1.00    inference(rectify,[],[f55])).
% 3.45/1.00  
% 3.45/1.00  fof(f57,plain,(
% 3.45/1.00    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0))))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f58,plain,(
% 3.45/1.00    ! [X0] : (((v2_funct_1(X0) | (sK1(X0) != sK2(X0) & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0)) & r2_hidden(sK2(X0),k1_relat_1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f56,f57])).
% 3.45/1.00  
% 3.45/1.00  fof(f81,plain,(
% 3.45/1.00    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f58])).
% 3.45/1.00  
% 3.45/1.00  fof(f1,axiom,(
% 3.45/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f48,plain,(
% 3.45/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.45/1.00    inference(nnf_transformation,[],[f1])).
% 3.45/1.00  
% 3.45/1.00  fof(f49,plain,(
% 3.45/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/1.00    inference(rectify,[],[f48])).
% 3.45/1.00  
% 3.45/1.00  fof(f50,plain,(
% 3.45/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f51,plain,(
% 3.45/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 3.45/1.00  
% 3.45/1.00  fof(f64,plain,(
% 3.45/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f51])).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2,plain,
% 3.45/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1838,plain,
% 3.45/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7,plain,
% 3.45/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1834,plain,
% 3.45/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.45/1.00      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6,plain,
% 3.45/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1835,plain,
% 3.45/1.00      ( X0 = X1
% 3.45/1.00      | v1_xboole_0(X0) != iProver_top
% 3.45/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3431,plain,
% 3.45/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1838,c_1835]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3730,plain,
% 3.45/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1834,c_3431]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3739,plain,
% 3.45/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1838,c_3730]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_31,plain,
% 3.45/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1820,plain,
% 3.45/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3903,plain,
% 3.45/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3739,c_1820]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_23,plain,
% 3.45/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10,plain,
% 3.45/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_458,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.45/1.00      | ~ v1_relat_1(X0) ),
% 3.45/1.00      inference(resolution,[status(thm)],[c_23,c_10]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_21,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_462,plain,
% 3.45/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.45/1.00      inference(global_propositional_subsumption,[status(thm)],[c_458,c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_463,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_462]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1811,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3947,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3739,c_1811]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6962,plain,
% 3.45/1.00      ( r1_tarski(k1_relat_1(k6_partfun1(k1_xboole_0)),X0) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3903,c_3947]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_14,plain,
% 3.45/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6964,plain,
% 3.45/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_6962,c_14]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_29,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.45/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | ~ v1_funct_1(X3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1822,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.45/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.45/1.00      | v1_funct_1(X0) != iProver_top
% 3.45/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_26,plain,
% 3.45/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | X3 = X2 ),
% 3.45/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_36,negated_conjecture,
% 3.45/1.00      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_580,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | X3 = X0
% 3.45/1.00      | k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) != X0
% 3.45/1.00      | k6_partfun1(sK3) != X3
% 3.45/1.00      | sK3 != X2
% 3.45/1.00      | sK3 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_581,plain,
% 3.45/1.00      ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 3.45/1.00      | ~ m1_subset_1(k6_partfun1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 3.45/1.00      | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_580]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_589,plain,
% 3.45/1.00      ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 3.45/1.00      | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
% 3.45/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_581,c_31]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1807,plain,
% 3.45/1.00      ( k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.45/1.00      | m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5419,plain,
% 3.45/1.00      ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3)
% 3.45/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.45/1.00      | v1_funct_1(sK5) != iProver_top
% 3.45/1.00      | v1_funct_1(sK6) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1822,c_1807]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_42,negated_conjecture,
% 3.45/1.00      ( v1_funct_1(sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_43,plain,
% 3.45/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_40,negated_conjecture,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_45,plain,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_39,negated_conjecture,
% 3.45/1.00      ( v1_funct_1(sK6) ),
% 3.45/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_46,plain,
% 3.45/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_37,negated_conjecture,
% 3.45/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_48,plain,
% 3.45/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5596,plain,
% 3.45/1.00      ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_5419,c_43,c_45,c_46,c_48]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_34,plain,
% 3.45/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.45/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | ~ v1_funct_1(X3)
% 3.45/1.00      | v2_funct_1(X3)
% 3.45/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.45/1.00      | k1_xboole_0 = X2 ),
% 3.45/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1818,plain,
% 3.45/1.00      ( k1_xboole_0 = X0
% 3.45/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.45/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.45/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.45/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.45/1.00      | v1_funct_1(X1) != iProver_top
% 3.45/1.00      | v1_funct_1(X3) != iProver_top
% 3.45/1.00      | v2_funct_1(X3) = iProver_top
% 3.45/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5622,plain,
% 3.45/1.00      ( sK3 = k1_xboole_0
% 3.45/1.00      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.45/1.00      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.45/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.45/1.00      | v1_funct_1(sK5) != iProver_top
% 3.45/1.00      | v1_funct_1(sK6) != iProver_top
% 3.45/1.00      | v2_funct_1(k6_partfun1(sK3)) != iProver_top
% 3.45/1.00      | v2_funct_1(sK5) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_5596,c_1818]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_41,negated_conjecture,
% 3.45/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.45/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_44,plain,
% 3.45/1.00      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_38,negated_conjecture,
% 3.45/1.00      ( v1_funct_2(sK6,sK4,sK3) ),
% 3.45/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_47,plain,
% 3.45/1.00      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1817,plain,
% 3.45/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_24,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1823,plain,
% 3.45/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.45/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4040,plain,
% 3.45/1.00      ( k2_relset_1(sK4,sK3,sK6) = k2_relat_1(sK6) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1817,c_1823]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_32,plain,
% 3.45/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.45/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.45/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.45/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | ~ v1_funct_1(X3)
% 3.45/1.00      | ~ v1_funct_1(X2)
% 3.45/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_593,plain,
% 3.45/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.45/1.00      | ~ v1_funct_1(X3)
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.45/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.45/1.00      | k6_partfun1(X1) != k6_partfun1(sK3)
% 3.45/1.00      | sK3 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_594,plain,
% 3.45/1.00      ( ~ v1_funct_2(X0,X1,sK3)
% 3.45/1.00      | ~ v1_funct_2(X2,sK3,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.45/1.00      | ~ v1_funct_1(X2)
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.45/1.00      | k2_relset_1(X1,sK3,X0) = sK3
% 3.45/1.00      | k6_partfun1(sK3) != k6_partfun1(sK3) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_593]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_834,plain,
% 3.45/1.00      ( ~ v1_funct_2(X0,X1,sK3)
% 3.45/1.00      | ~ v1_funct_2(X2,sK3,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 3.45/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | ~ v1_funct_1(X2)
% 3.45/1.00      | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.45/1.00      | k2_relset_1(X1,sK3,X0) = sK3 ),
% 3.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_594]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1806,plain,
% 3.45/1.00      ( k1_partfun1(sK3,X0,X0,sK3,X1,X2) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.45/1.00      | k2_relset_1(X0,sK3,X2) = sK3
% 3.45/1.00      | v1_funct_2(X2,X0,sK3) != iProver_top
% 3.45/1.00      | v1_funct_2(X1,sK3,X0) != iProver_top
% 3.45/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.45/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 3.45/1.00      | v1_funct_1(X2) != iProver_top
% 3.45/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2606,plain,
% 3.45/1.00      ( k2_relset_1(sK4,sK3,sK6) = sK3
% 3.45/1.00      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.45/1.00      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.45/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.45/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.45/1.00      | v1_funct_1(sK5) != iProver_top
% 3.45/1.00      | v1_funct_1(sK6) != iProver_top ),
% 3.45/1.00      inference(equality_resolution,[status(thm)],[c_1806]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2609,plain,
% 3.45/1.00      ( k2_relset_1(sK4,sK3,sK6) = sK3 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_2606,c_43,c_44,c_45,c_46,c_47,c_48]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4050,plain,
% 3.45/1.00      ( k2_relat_1(sK6) = sK3 ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_4040,c_2609]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_22,plain,
% 3.45/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_27,plain,
% 3.45/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.45/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.45/1.00      | ~ v1_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_498,plain,
% 3.45/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.45/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.45/1.00      | ~ v1_relat_1(X0)
% 3.45/1.00      | X0 != X1
% 3.45/1.00      | k2_relat_1(X0) != X3 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_499,plain,
% 3.45/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.45/1.00      | ~ v1_relat_1(X0) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_498]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_509,plain,
% 3.45/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.45/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_499,c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_35,negated_conjecture,
% 3.45/1.00      ( ~ v2_funct_2(sK6,sK3) | ~ v2_funct_1(sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_524,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.45/1.00      | ~ v2_funct_1(sK5)
% 3.45/1.00      | k2_relat_1(X0) != sK3
% 3.45/1.00      | sK6 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_509,c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_525,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6))))
% 3.45/1.00      | ~ v2_funct_1(sK5)
% 3.45/1.00      | k2_relat_1(sK6) != sK3 ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_524]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1171,plain,
% 3.45/1.00      ( ~ v2_funct_1(sK5) | sP0_iProver_split | k2_relat_1(sK6) != sK3 ),
% 3.45/1.00      inference(splitting,
% 3.45/1.00                [splitting(split),new_symbols(definition,[])],
% 3.45/1.00                [c_525]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1809,plain,
% 3.45/1.00      ( k2_relat_1(sK6) != sK3
% 3.45/1.00      | v2_funct_1(sK5) != iProver_top
% 3.45/1.00      | sP0_iProver_split = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4240,plain,
% 3.45/1.00      ( sK3 != sK3
% 3.45/1.00      | v2_funct_1(sK5) != iProver_top
% 3.45/1.00      | sP0_iProver_split = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_4050,c_1809]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4241,plain,
% 3.45/1.00      ( v2_funct_1(sK5) != iProver_top | sP0_iProver_split = iProver_top ),
% 3.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_4240]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1170,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6))))
% 3.45/1.00      | ~ sP0_iProver_split ),
% 3.45/1.00      inference(splitting,
% 3.45/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.45/1.00                [c_525]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1810,plain,
% 3.45/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6)))) != iProver_top
% 3.45/1.00      | sP0_iProver_split != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4239,plain,
% 3.45/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.45/1.00      | sP0_iProver_split != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_4050,c_1810]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4487,plain,
% 3.45/1.00      ( sP0_iProver_split != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1817,c_4239]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5731,plain,
% 3.45/1.00      ( v2_funct_1(k6_partfun1(sK3)) != iProver_top | sK3 = k1_xboole_0 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_5622,c_43,c_44,c_45,c_46,c_47,c_48,c_4241,c_4487]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5732,plain,
% 3.45/1.00      ( sK3 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK3)) != iProver_top ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_5731]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_20,plain,
% 3.45/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1825,plain,
% 3.45/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5737,plain,
% 3.45/1.00      ( sK3 = k1_xboole_0 ),
% 3.45/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5732,c_1825]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1814,plain,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3946,plain,
% 3.45/1.00      ( r1_tarski(k1_relat_1(sK5),sK3) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1814,c_1811]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.45/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1837,plain,
% 3.45/1.00      ( X0 = X1
% 3.45/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.45/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4207,plain,
% 3.45/1.00      ( k1_relat_1(sK5) = sK3 | r1_tarski(sK3,k1_relat_1(sK5)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3946,c_1837]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_5747,plain,
% 3.45/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 3.45/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(sK5)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_5737,c_4207]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2164,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.45/1.00      | v1_relat_1(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_17,plain,
% 3.45/1.00      ( r2_hidden(sK2(X0),k1_relat_1(X0))
% 3.45/1.00      | ~ v1_funct_1(X0)
% 3.45/1.00      | v2_funct_1(X0)
% 3.45/1.00      | ~ v1_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2195,plain,
% 3.45/1.00      ( r2_hidden(sK2(sK5),k1_relat_1(sK5))
% 3.45/1.00      | ~ v1_funct_1(sK5)
% 3.45/1.00      | v2_funct_1(sK5)
% 3.45/1.00      | ~ v1_relat_1(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4253,plain,
% 3.45/1.00      ( ~ v2_funct_1(sK5) | sP0_iProver_split ),
% 3.45/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4241]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1175,plain,
% 3.45/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.45/1.00      theory(equality) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4264,plain,
% 3.45/1.00      ( ~ v1_xboole_0(X0)
% 3.45/1.00      | v1_xboole_0(k1_relat_1(sK5))
% 3.45/1.00      | k1_relat_1(sK5) != X0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1175]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4266,plain,
% 3.45/1.00      ( v1_xboole_0(k1_relat_1(sK5))
% 3.45/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.45/1.00      | k1_relat_1(sK5) != k1_xboole_0 ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_4264]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4488,plain,
% 3.45/1.00      ( ~ sP0_iProver_split ),
% 3.45/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4487]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1,plain,
% 3.45/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4789,plain,
% 3.45/1.00      ( ~ r2_hidden(sK2(sK5),k1_relat_1(sK5))
% 3.45/1.00      | ~ v1_xboole_0(k1_relat_1(sK5)) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6769,plain,
% 3.45/1.00      ( r1_tarski(k1_xboole_0,k1_relat_1(sK5)) != iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_5747,c_42,c_40,c_2,c_2164,c_2195,c_4253,c_4266,c_4488,
% 3.45/1.00                 c_4789]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6975,plain,
% 3.45/1.00      ( $false ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_6964,c_6769]) ).
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  ------                               Statistics
% 3.45/1.00  
% 3.45/1.00  ------ General
% 3.45/1.00  
% 3.45/1.00  abstr_ref_over_cycles:                  0
% 3.45/1.00  abstr_ref_under_cycles:                 0
% 3.45/1.00  gc_basic_clause_elim:                   0
% 3.45/1.00  forced_gc_time:                         0
% 3.45/1.00  parsing_time:                           0.009
% 3.45/1.00  unif_index_cands_time:                  0.
% 3.45/1.00  unif_index_add_time:                    0.
% 3.45/1.00  orderings_time:                         0.
% 3.45/1.00  out_proof_time:                         0.011
% 3.45/1.00  total_time:                             0.244
% 3.45/1.00  num_of_symbols:                         60
% 3.45/1.00  num_of_terms:                           7521
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing
% 3.45/1.00  
% 3.45/1.00  num_of_splits:                          1
% 3.45/1.00  num_of_split_atoms:                     1
% 3.45/1.00  num_of_reused_defs:                     0
% 3.45/1.00  num_eq_ax_congr_red:                    28
% 3.45/1.00  num_of_sem_filtered_clauses:            1
% 3.45/1.00  num_of_subtypes:                        0
% 3.45/1.00  monotx_restored_types:                  0
% 3.45/1.00  sat_num_of_epr_types:                   0
% 3.45/1.00  sat_num_of_non_cyclic_types:            0
% 3.45/1.00  sat_guarded_non_collapsed_types:        0
% 3.45/1.00  num_pure_diseq_elim:                    0
% 3.45/1.00  simp_replaced_by:                       0
% 3.45/1.00  res_preprocessed:                       187
% 3.45/1.00  prep_upred:                             0
% 3.45/1.00  prep_unflattend:                        19
% 3.45/1.00  smt_new_axioms:                         0
% 3.45/1.00  pred_elim_cands:                        8
% 3.45/1.00  pred_elim:                              4
% 3.45/1.00  pred_elim_cl:                           6
% 3.45/1.00  pred_elim_cycles:                       6
% 3.45/1.00  merged_defs:                            0
% 3.45/1.00  merged_defs_ncl:                        0
% 3.45/1.00  bin_hyper_res:                          0
% 3.45/1.00  prep_cycles:                            4
% 3.45/1.00  pred_elim_time:                         0.011
% 3.45/1.00  splitting_time:                         0.
% 3.45/1.00  sem_filter_time:                        0.
% 3.45/1.00  monotx_time:                            0.
% 3.45/1.00  subtype_inf_time:                       0.
% 3.45/1.00  
% 3.45/1.00  ------ Problem properties
% 3.45/1.00  
% 3.45/1.00  clauses:                                37
% 3.45/1.00  conjectures:                            6
% 3.45/1.00  epr:                                    9
% 3.45/1.00  horn:                                   32
% 3.45/1.00  ground:                                 9
% 3.45/1.00  unary:                                  12
% 3.45/1.00  binary:                                 8
% 3.45/1.00  lits:                                   112
% 3.45/1.00  lits_eq:                                20
% 3.45/1.00  fd_pure:                                0
% 3.45/1.00  fd_pseudo:                              0
% 3.45/1.00  fd_cond:                                3
% 3.45/1.00  fd_pseudo_cond:                         3
% 3.45/1.00  ac_symbols:                             0
% 3.45/1.00  
% 3.45/1.00  ------ Propositional Solver
% 3.45/1.00  
% 3.45/1.00  prop_solver_calls:                      26
% 3.45/1.00  prop_fast_solver_calls:                 1454
% 3.45/1.00  smt_solver_calls:                       0
% 3.45/1.00  smt_fast_solver_calls:                  0
% 3.45/1.00  prop_num_of_clauses:                    2568
% 3.45/1.00  prop_preprocess_simplified:             8852
% 3.45/1.00  prop_fo_subsumed:                       31
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
% 3.45/1.00  inst_num_of_clauses:                    803
% 3.45/1.00  inst_num_in_passive:                    143
% 3.45/1.00  inst_num_in_active:                     365
% 3.45/1.00  inst_num_in_unprocessed:                295
% 3.45/1.00  inst_num_of_loops:                      430
% 3.45/1.00  inst_num_of_learning_restarts:          0
% 3.45/1.00  inst_num_moves_active_passive:          64
% 3.45/1.00  inst_lit_activity:                      0
% 3.45/1.00  inst_lit_activity_moves:                0
% 3.45/1.00  inst_num_tautologies:                   0
% 3.45/1.00  inst_num_prop_implied:                  0
% 3.45/1.00  inst_num_existing_simplified:           0
% 3.45/1.00  inst_num_eq_res_simplified:             0
% 3.45/1.00  inst_num_child_elim:                    0
% 3.45/1.00  inst_num_of_dismatching_blockings:      52
% 3.45/1.00  inst_num_of_non_proper_insts:           591
% 3.45/1.00  inst_num_of_duplicates:                 0
% 3.45/1.00  inst_inst_num_from_inst_to_res:         0
% 3.45/1.00  inst_dismatching_checking_time:         0.
% 3.45/1.00  
% 3.45/1.00  ------ Resolution
% 3.45/1.00  
% 3.45/1.00  res_num_of_clauses:                     0
% 3.45/1.00  res_num_in_passive:                     0
% 3.45/1.00  res_num_in_active:                      0
% 3.45/1.00  res_num_of_loops:                       191
% 3.45/1.00  res_forward_subset_subsumed:            44
% 3.45/1.00  res_backward_subset_subsumed:           0
% 3.45/1.00  res_forward_subsumed:                   0
% 3.45/1.00  res_backward_subsumed:                  0
% 3.45/1.00  res_forward_subsumption_resolution:     4
% 3.45/1.00  res_backward_subsumption_resolution:    0
% 3.45/1.00  res_clause_to_clause_subsumption:       185
% 3.45/1.00  res_orphan_elimination:                 0
% 3.45/1.00  res_tautology_del:                      23
% 3.45/1.00  res_num_eq_res_simplified:              1
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
% 3.45/1.00  sup_num_of_clauses:                     88
% 3.45/1.00  sup_num_in_active:                      64
% 3.45/1.00  sup_num_in_passive:                     24
% 3.45/1.00  sup_num_of_loops:                       85
% 3.45/1.00  sup_fw_superposition:                   44
% 3.45/1.00  sup_bw_superposition:                   36
% 3.45/1.00  sup_immediate_simplified:               28
% 3.45/1.00  sup_given_eliminated:                   0
% 3.45/1.00  comparisons_done:                       0
% 3.45/1.00  comparisons_avoided:                    0
% 3.45/1.00  
% 3.45/1.00  ------ Simplifications
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  sim_fw_subset_subsumed:                 4
% 3.45/1.00  sim_bw_subset_subsumed:                 0
% 3.45/1.00  sim_fw_subsumed:                        5
% 3.45/1.00  sim_bw_subsumed:                        0
% 3.45/1.00  sim_fw_subsumption_res:                 1
% 3.45/1.00  sim_bw_subsumption_res:                 0
% 3.45/1.00  sim_tautology_del:                      3
% 3.45/1.00  sim_eq_tautology_del:                   4
% 3.45/1.00  sim_eq_res_simp:                        2
% 3.45/1.00  sim_fw_demodulated:                     8
% 3.45/1.00  sim_bw_demodulated:                     29
% 3.45/1.00  sim_light_normalised:                   5
% 3.45/1.00  sim_joinable_taut:                      0
% 3.45/1.00  sim_joinable_simp:                      0
% 3.45/1.00  sim_ac_normalised:                      0
% 3.45/1.00  sim_smt_subsumption:                    0
% 3.45/1.00  
%------------------------------------------------------------------------------
