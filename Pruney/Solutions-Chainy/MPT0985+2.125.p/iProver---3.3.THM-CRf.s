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
% DateTime   : Thu Dec  3 12:02:45 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  213 (3258 expanded)
%              Number of clauses        :  138 (1114 expanded)
%              Number of leaves         :   19 ( 610 expanded)
%              Depth                    :   26
%              Number of atoms          :  587 (16588 expanded)
%              Number of equality atoms :  330 (3675 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f115,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
        | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
        | ~ v1_funct_1(k2_funct_1(sK7)) )
      & k2_relset_1(sK5,sK6,sK7) = sK6
      & v2_funct_1(sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
      | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
      | ~ v1_funct_1(k2_funct_1(sK7)) )
    & k2_relset_1(sK5,sK6,sK7) = sK6
    & v2_funct_1(sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f44,f61])).

fof(f107,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f108,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f87,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f106,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    k2_relset_1(sK5,sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f62])).

fof(f86,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(cnf_transformation,[],[f62])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f121,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f84,f102])).

fof(f85,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f112,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f85,f102])).

fof(f79,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_34,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1915,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2790,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1915])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1929,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2998,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2790,c_1929])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1931,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3239,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2998,c_1931])).

cnf(c_3242,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3239,c_2790])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1917,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3774,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1917])).

cnf(c_4924,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3242,c_3774])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4932,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4924,c_16])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_893,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X1
    | sK6 != X2
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_46])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_896,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_894,c_45])).

cnf(c_1910,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3771,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1910,c_1917])).

cnf(c_3928,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_896,c_3771])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3477,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_1918])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_44,negated_conjecture,
    ( v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_579,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_44])).

cnf(c_580,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_582,plain,
    ( ~ v1_relat_1(sK7)
    | k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_47])).

cnf(c_1906,plain,
    ( k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7)
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_3592,plain,
    ( k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_3477,c_1906])).

cnf(c_39,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1911,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3691,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k1_relat_1(sK7)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top
    | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3592,c_1911])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1916,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3406,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1910,c_1916])).

cnf(c_43,negated_conjecture,
    ( k2_relset_1(sK5,sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3418,plain,
    ( k2_relat_1(sK7) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_3406,c_43])).

cnf(c_24,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_565,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_44])).

cnf(c_566,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k1_relat_1(k2_funct_1(sK7)) = k2_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_568,plain,
    ( ~ v1_relat_1(sK7)
    | k1_relat_1(k2_funct_1(sK7)) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_47])).

cnf(c_1907,plain,
    ( k1_relat_1(k2_funct_1(sK7)) = k2_relat_1(sK7)
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_3460,plain,
    ( k1_relat_1(k2_funct_1(sK7)) = sK6
    | v1_relat_1(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3418,c_1907])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_2296,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2297,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2296])).

cnf(c_3662,plain,
    ( k1_relat_1(k2_funct_1(sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_50,c_2297])).

cnf(c_3692,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top
    | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3691,c_3662])).

cnf(c_48,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2268,plain,
    ( v1_funct_1(k2_funct_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2269,plain,
    ( v1_funct_1(k2_funct_1(sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2281,plain,
    ( ~ v1_funct_1(sK7)
    | v1_relat_1(k2_funct_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2282,plain,
    ( v1_funct_1(sK7) != iProver_top
    | v1_relat_1(k2_funct_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2281])).

cnf(c_4205,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3692,c_48,c_50,c_2269,c_2282,c_2297])).

cnf(c_4213,plain,
    ( k1_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = k1_relat_1(k2_funct_1(sK7)) ),
    inference(superposition,[status(thm)],[c_4205,c_1917])).

cnf(c_4219,plain,
    ( k1_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_4213,c_3662])).

cnf(c_4233,plain,
    ( k1_relset_1(sK6,sK5,k2_funct_1(sK7)) = sK6
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3928,c_4219])).

cnf(c_40,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_42,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_917,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK7))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK7) != X0
    | k1_relat_1(X0) != sK6
    | k2_relat_1(X0) != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_42])).

cnf(c_918,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_1(k2_funct_1(sK7))
    | ~ v1_relat_1(k2_funct_1(sK7))
    | k1_relat_1(k2_funct_1(sK7)) != sK6
    | k2_relat_1(k2_funct_1(sK7)) != sK5 ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_930,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_1(k2_funct_1(sK7))
    | k1_relat_1(k2_funct_1(sK7)) != sK6
    | k2_relat_1(k2_funct_1(sK7)) != sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_918,c_25])).

cnf(c_1897,plain,
    ( k1_relat_1(k2_funct_1(sK7)) != sK6
    | k2_relat_1(k2_funct_1(sK7)) != sK5
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_919,plain,
    ( k1_relat_1(k2_funct_1(sK7)) != sK6
    | k2_relat_1(k2_funct_1(sK7)) != sK5
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top
    | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_2410,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | k2_relat_1(k2_funct_1(sK7)) != sK5
    | k1_relat_1(k2_funct_1(sK7)) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1897,c_48,c_50,c_919,c_2269,c_2282,c_2297])).

cnf(c_2411,plain,
    ( k1_relat_1(k2_funct_1(sK7)) != sK6
    | k2_relat_1(k2_funct_1(sK7)) != sK5
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2410])).

cnf(c_3665,plain,
    ( k2_relat_1(k2_funct_1(sK7)) != sK5
    | sK6 != sK6
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3662,c_2411])).

cnf(c_3712,plain,
    ( k2_relat_1(k2_funct_1(sK7)) != sK5
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3665])).

cnf(c_3714,plain,
    ( k1_relat_1(sK7) != sK5
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3712,c_3592])).

cnf(c_4009,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3928,c_3714])).

cnf(c_4210,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3928,c_4205])).

cnf(c_4479,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4233,c_4009,c_4210])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1923,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3816,plain,
    ( k2_funct_1(sK7) = k1_xboole_0
    | sK6 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3662,c_1923])).

cnf(c_4124,plain,
    ( sK6 != k1_xboole_0
    | k2_funct_1(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3816,c_48,c_50,c_2282,c_2297])).

cnf(c_4125,plain,
    ( k2_funct_1(sK7) = k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4124])).

cnf(c_4484,plain,
    ( k2_funct_1(sK7) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4479,c_4125])).

cnf(c_4621,plain,
    ( k2_funct_1(sK7) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4484])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1924,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3849,plain,
    ( sK6 != k1_xboole_0
    | sK7 = k1_xboole_0
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3418,c_1924])).

cnf(c_3863,plain,
    ( ~ v1_relat_1(sK7)
    | sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3849])).

cnf(c_4001,plain,
    ( sK7 = k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3849,c_45,c_2296,c_3863])).

cnf(c_4002,plain,
    ( sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4001])).

cnf(c_4485,plain,
    ( sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4479,c_4002])).

cnf(c_4571,plain,
    ( sK7 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4485])).

cnf(c_4622,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4621,c_4571])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_810,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_1(k2_funct_1(sK7))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK7) != X0
    | sK5 != X1
    | sK6 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_42])).

cnf(c_811,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | ~ v1_funct_1(k2_funct_1(sK7))
    | k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_1902,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
    | sK6 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_2142,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
    | sK6 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1902,c_7])).

cnf(c_2488,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | sK6 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2142,c_48,c_50,c_2269,c_2297])).

cnf(c_2489,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
    | sK6 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2488])).

cnf(c_4497,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4479,c_2489])).

cnf(c_4535,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4497])).

cnf(c_4539,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4535,c_7])).

cnf(c_4580,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4571,c_4539])).

cnf(c_4626,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4622,c_4580])).

cnf(c_22,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_108,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_110,plain,
    ( v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_21,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_111,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_113,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_1020,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2300,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_2301,plain,
    ( X0 != k6_partfun1(X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2300])).

cnf(c_2303,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_1022,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2325,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_2326,plain,
    ( X0 != k6_partfun1(X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2325])).

cnf(c_2328,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2326])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2916,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1911])).

cnf(c_2920,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2916,c_16])).

cnf(c_2921,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2920,c_7])).

cnf(c_3029,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2998])).

cnf(c_3075,plain,
    ( ~ r1_tarski(k6_partfun1(X0),k1_xboole_0)
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3077,plain,
    ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3075])).

cnf(c_4872,plain,
    ( k1_relset_1(k1_xboole_0,sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4626,c_110,c_113,c_2303,c_2328,c_2921,c_3029,c_3077])).

cnf(c_4940,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4932,c_4872])).

cnf(c_141,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_140,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4940,c_141,c_140])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:47:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.89/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/0.99  
% 2.89/0.99  ------  iProver source info
% 2.89/0.99  
% 2.89/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.89/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/0.99  git: non_committed_changes: false
% 2.89/0.99  git: last_make_outside_of_git: false
% 2.89/0.99  
% 2.89/0.99  ------ 
% 2.89/0.99  
% 2.89/0.99  ------ Input Options
% 2.89/0.99  
% 2.89/0.99  --out_options                           all
% 2.89/0.99  --tptp_safe_out                         true
% 2.89/0.99  --problem_path                          ""
% 2.89/0.99  --include_path                          ""
% 2.89/0.99  --clausifier                            res/vclausify_rel
% 2.89/0.99  --clausifier_options                    --mode clausify
% 2.89/0.99  --stdin                                 false
% 2.89/0.99  --stats_out                             all
% 2.89/0.99  
% 2.89/0.99  ------ General Options
% 2.89/0.99  
% 2.89/0.99  --fof                                   false
% 2.89/0.99  --time_out_real                         305.
% 2.89/0.99  --time_out_virtual                      -1.
% 2.89/0.99  --symbol_type_check                     false
% 2.89/0.99  --clausify_out                          false
% 2.89/0.99  --sig_cnt_out                           false
% 2.89/0.99  --trig_cnt_out                          false
% 2.89/0.99  --trig_cnt_out_tolerance                1.
% 2.89/0.99  --trig_cnt_out_sk_spl                   false
% 2.89/0.99  --abstr_cl_out                          false
% 2.89/0.99  
% 2.89/0.99  ------ Global Options
% 2.89/0.99  
% 2.89/0.99  --schedule                              default
% 2.89/0.99  --add_important_lit                     false
% 2.89/0.99  --prop_solver_per_cl                    1000
% 2.89/0.99  --min_unsat_core                        false
% 2.89/0.99  --soft_assumptions                      false
% 2.89/0.99  --soft_lemma_size                       3
% 2.89/0.99  --prop_impl_unit_size                   0
% 2.89/0.99  --prop_impl_unit                        []
% 2.89/0.99  --share_sel_clauses                     true
% 2.89/0.99  --reset_solvers                         false
% 2.89/0.99  --bc_imp_inh                            [conj_cone]
% 2.89/0.99  --conj_cone_tolerance                   3.
% 2.89/0.99  --extra_neg_conj                        none
% 2.89/0.99  --large_theory_mode                     true
% 2.89/0.99  --prolific_symb_bound                   200
% 2.89/0.99  --lt_threshold                          2000
% 2.89/0.99  --clause_weak_htbl                      true
% 2.89/0.99  --gc_record_bc_elim                     false
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing Options
% 2.89/0.99  
% 2.89/0.99  --preprocessing_flag                    true
% 2.89/0.99  --time_out_prep_mult                    0.1
% 2.89/0.99  --splitting_mode                        input
% 2.89/0.99  --splitting_grd                         true
% 2.89/0.99  --splitting_cvd                         false
% 2.89/0.99  --splitting_cvd_svl                     false
% 2.89/0.99  --splitting_nvd                         32
% 2.89/0.99  --sub_typing                            true
% 2.89/0.99  --prep_gs_sim                           true
% 2.89/0.99  --prep_unflatten                        true
% 2.89/0.99  --prep_res_sim                          true
% 2.89/0.99  --prep_upred                            true
% 2.89/0.99  --prep_sem_filter                       exhaustive
% 2.89/0.99  --prep_sem_filter_out                   false
% 2.89/0.99  --pred_elim                             true
% 2.89/0.99  --res_sim_input                         true
% 2.89/0.99  --eq_ax_congr_red                       true
% 2.89/0.99  --pure_diseq_elim                       true
% 2.89/0.99  --brand_transform                       false
% 2.89/0.99  --non_eq_to_eq                          false
% 2.89/0.99  --prep_def_merge                        true
% 2.89/0.99  --prep_def_merge_prop_impl              false
% 2.89/0.99  --prep_def_merge_mbd                    true
% 2.89/0.99  --prep_def_merge_tr_red                 false
% 2.89/0.99  --prep_def_merge_tr_cl                  false
% 2.89/0.99  --smt_preprocessing                     true
% 2.89/0.99  --smt_ac_axioms                         fast
% 2.89/0.99  --preprocessed_out                      false
% 2.89/0.99  --preprocessed_stats                    false
% 2.89/0.99  
% 2.89/0.99  ------ Abstraction refinement Options
% 2.89/0.99  
% 2.89/0.99  --abstr_ref                             []
% 2.89/0.99  --abstr_ref_prep                        false
% 2.89/0.99  --abstr_ref_until_sat                   false
% 2.89/0.99  --abstr_ref_sig_restrict                funpre
% 2.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.99  --abstr_ref_under                       []
% 2.89/0.99  
% 2.89/0.99  ------ SAT Options
% 2.89/0.99  
% 2.89/0.99  --sat_mode                              false
% 2.89/0.99  --sat_fm_restart_options                ""
% 2.89/0.99  --sat_gr_def                            false
% 2.89/0.99  --sat_epr_types                         true
% 2.89/0.99  --sat_non_cyclic_types                  false
% 2.89/0.99  --sat_finite_models                     false
% 2.89/0.99  --sat_fm_lemmas                         false
% 2.89/0.99  --sat_fm_prep                           false
% 2.89/0.99  --sat_fm_uc_incr                        true
% 2.89/0.99  --sat_out_model                         small
% 2.89/0.99  --sat_out_clauses                       false
% 2.89/0.99  
% 2.89/0.99  ------ QBF Options
% 2.89/0.99  
% 2.89/0.99  --qbf_mode                              false
% 2.89/0.99  --qbf_elim_univ                         false
% 2.89/0.99  --qbf_dom_inst                          none
% 2.89/0.99  --qbf_dom_pre_inst                      false
% 2.89/0.99  --qbf_sk_in                             false
% 2.89/0.99  --qbf_pred_elim                         true
% 2.89/0.99  --qbf_split                             512
% 2.89/0.99  
% 2.89/0.99  ------ BMC1 Options
% 2.89/0.99  
% 2.89/0.99  --bmc1_incremental                      false
% 2.89/0.99  --bmc1_axioms                           reachable_all
% 2.89/0.99  --bmc1_min_bound                        0
% 2.89/0.99  --bmc1_max_bound                        -1
% 2.89/0.99  --bmc1_max_bound_default                -1
% 2.89/0.99  --bmc1_symbol_reachability              true
% 2.89/0.99  --bmc1_property_lemmas                  false
% 2.89/0.99  --bmc1_k_induction                      false
% 2.89/0.99  --bmc1_non_equiv_states                 false
% 2.89/0.99  --bmc1_deadlock                         false
% 2.89/0.99  --bmc1_ucm                              false
% 2.89/0.99  --bmc1_add_unsat_core                   none
% 2.89/0.99  --bmc1_unsat_core_children              false
% 2.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.99  --bmc1_out_stat                         full
% 2.89/0.99  --bmc1_ground_init                      false
% 2.89/0.99  --bmc1_pre_inst_next_state              false
% 2.89/0.99  --bmc1_pre_inst_state                   false
% 2.89/0.99  --bmc1_pre_inst_reach_state             false
% 2.89/0.99  --bmc1_out_unsat_core                   false
% 2.89/0.99  --bmc1_aig_witness_out                  false
% 2.89/0.99  --bmc1_verbose                          false
% 2.89/0.99  --bmc1_dump_clauses_tptp                false
% 2.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.99  --bmc1_dump_file                        -
% 2.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.99  --bmc1_ucm_extend_mode                  1
% 2.89/0.99  --bmc1_ucm_init_mode                    2
% 2.89/0.99  --bmc1_ucm_cone_mode                    none
% 2.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.99  --bmc1_ucm_relax_model                  4
% 2.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.99  --bmc1_ucm_layered_model                none
% 2.89/0.99  --bmc1_ucm_max_lemma_size               10
% 2.89/0.99  
% 2.89/0.99  ------ AIG Options
% 2.89/0.99  
% 2.89/0.99  --aig_mode                              false
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation Options
% 2.89/0.99  
% 2.89/0.99  --instantiation_flag                    true
% 2.89/0.99  --inst_sos_flag                         false
% 2.89/0.99  --inst_sos_phase                        true
% 2.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel_side                     num_symb
% 2.89/0.99  --inst_solver_per_active                1400
% 2.89/0.99  --inst_solver_calls_frac                1.
% 2.89/0.99  --inst_passive_queue_type               priority_queues
% 2.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.99  --inst_passive_queues_freq              [25;2]
% 2.89/0.99  --inst_dismatching                      true
% 2.89/0.99  --inst_eager_unprocessed_to_passive     true
% 2.89/0.99  --inst_prop_sim_given                   true
% 2.89/0.99  --inst_prop_sim_new                     false
% 2.89/0.99  --inst_subs_new                         false
% 2.89/0.99  --inst_eq_res_simp                      false
% 2.89/0.99  --inst_subs_given                       false
% 2.89/0.99  --inst_orphan_elimination               true
% 2.89/0.99  --inst_learning_loop_flag               true
% 2.89/0.99  --inst_learning_start                   3000
% 2.89/0.99  --inst_learning_factor                  2
% 2.89/0.99  --inst_start_prop_sim_after_learn       3
% 2.89/0.99  --inst_sel_renew                        solver
% 2.89/0.99  --inst_lit_activity_flag                true
% 2.89/0.99  --inst_restr_to_given                   false
% 2.89/0.99  --inst_activity_threshold               500
% 2.89/0.99  --inst_out_proof                        true
% 2.89/0.99  
% 2.89/0.99  ------ Resolution Options
% 2.89/0.99  
% 2.89/0.99  --resolution_flag                       true
% 2.89/0.99  --res_lit_sel                           adaptive
% 2.89/0.99  --res_lit_sel_side                      none
% 2.89/0.99  --res_ordering                          kbo
% 2.89/0.99  --res_to_prop_solver                    active
% 2.89/0.99  --res_prop_simpl_new                    false
% 2.89/0.99  --res_prop_simpl_given                  true
% 2.89/0.99  --res_passive_queue_type                priority_queues
% 2.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.99  --res_passive_queues_freq               [15;5]
% 2.89/0.99  --res_forward_subs                      full
% 2.89/0.99  --res_backward_subs                     full
% 2.89/0.99  --res_forward_subs_resolution           true
% 2.89/0.99  --res_backward_subs_resolution          true
% 2.89/0.99  --res_orphan_elimination                true
% 2.89/0.99  --res_time_limit                        2.
% 2.89/0.99  --res_out_proof                         true
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Options
% 2.89/0.99  
% 2.89/0.99  --superposition_flag                    true
% 2.89/0.99  --sup_passive_queue_type                priority_queues
% 2.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.99  --demod_completeness_check              fast
% 2.89/0.99  --demod_use_ground                      true
% 2.89/0.99  --sup_to_prop_solver                    passive
% 2.89/0.99  --sup_prop_simpl_new                    true
% 2.89/0.99  --sup_prop_simpl_given                  true
% 2.89/0.99  --sup_fun_splitting                     false
% 2.89/0.99  --sup_smt_interval                      50000
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Simplification Setup
% 2.89/0.99  
% 2.89/0.99  --sup_indices_passive                   []
% 2.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_full_bw                           [BwDemod]
% 2.89/0.99  --sup_immed_triv                        [TrivRules]
% 2.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_immed_bw_main                     []
% 2.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  
% 2.89/0.99  ------ Combination Options
% 2.89/0.99  
% 2.89/0.99  --comb_res_mult                         3
% 2.89/0.99  --comb_sup_mult                         2
% 2.89/0.99  --comb_inst_mult                        10
% 2.89/0.99  
% 2.89/0.99  ------ Debug Options
% 2.89/0.99  
% 2.89/0.99  --dbg_backtrace                         false
% 2.89/0.99  --dbg_dump_prop_clauses                 false
% 2.89/0.99  --dbg_dump_prop_clauses_file            -
% 2.89/0.99  --dbg_out_stat                          false
% 2.89/0.99  ------ Parsing...
% 2.89/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/0.99  ------ Proving...
% 2.89/0.99  ------ Problem Properties 
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  clauses                                 49
% 2.89/0.99  conjectures                             3
% 2.89/0.99  EPR                                     4
% 2.89/0.99  Horn                                    41
% 2.89/0.99  unary                                   15
% 2.89/0.99  binary                                  15
% 2.89/0.99  lits                                    113
% 2.89/0.99  lits eq                                 47
% 2.89/0.99  fd_pure                                 0
% 2.89/0.99  fd_pseudo                               0
% 2.89/0.99  fd_cond                                 5
% 2.89/0.99  fd_pseudo_cond                          2
% 2.89/0.99  AC symbols                              0
% 2.89/0.99  
% 2.89/0.99  ------ Schedule dynamic 5 is on 
% 2.89/0.99  
% 2.89/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  ------ 
% 2.89/0.99  Current options:
% 2.89/0.99  ------ 
% 2.89/0.99  
% 2.89/0.99  ------ Input Options
% 2.89/0.99  
% 2.89/0.99  --out_options                           all
% 2.89/0.99  --tptp_safe_out                         true
% 2.89/0.99  --problem_path                          ""
% 2.89/0.99  --include_path                          ""
% 2.89/0.99  --clausifier                            res/vclausify_rel
% 2.89/0.99  --clausifier_options                    --mode clausify
% 2.89/0.99  --stdin                                 false
% 2.89/0.99  --stats_out                             all
% 2.89/0.99  
% 2.89/0.99  ------ General Options
% 2.89/0.99  
% 2.89/0.99  --fof                                   false
% 2.89/0.99  --time_out_real                         305.
% 2.89/0.99  --time_out_virtual                      -1.
% 2.89/0.99  --symbol_type_check                     false
% 2.89/0.99  --clausify_out                          false
% 2.89/0.99  --sig_cnt_out                           false
% 2.89/0.99  --trig_cnt_out                          false
% 2.89/0.99  --trig_cnt_out_tolerance                1.
% 2.89/0.99  --trig_cnt_out_sk_spl                   false
% 2.89/0.99  --abstr_cl_out                          false
% 2.89/0.99  
% 2.89/0.99  ------ Global Options
% 2.89/0.99  
% 2.89/0.99  --schedule                              default
% 2.89/0.99  --add_important_lit                     false
% 2.89/0.99  --prop_solver_per_cl                    1000
% 2.89/0.99  --min_unsat_core                        false
% 2.89/0.99  --soft_assumptions                      false
% 2.89/0.99  --soft_lemma_size                       3
% 2.89/0.99  --prop_impl_unit_size                   0
% 2.89/0.99  --prop_impl_unit                        []
% 2.89/0.99  --share_sel_clauses                     true
% 2.89/0.99  --reset_solvers                         false
% 2.89/0.99  --bc_imp_inh                            [conj_cone]
% 2.89/0.99  --conj_cone_tolerance                   3.
% 2.89/0.99  --extra_neg_conj                        none
% 2.89/0.99  --large_theory_mode                     true
% 2.89/0.99  --prolific_symb_bound                   200
% 2.89/0.99  --lt_threshold                          2000
% 2.89/0.99  --clause_weak_htbl                      true
% 2.89/0.99  --gc_record_bc_elim                     false
% 2.89/0.99  
% 2.89/0.99  ------ Preprocessing Options
% 2.89/0.99  
% 2.89/0.99  --preprocessing_flag                    true
% 2.89/0.99  --time_out_prep_mult                    0.1
% 2.89/0.99  --splitting_mode                        input
% 2.89/0.99  --splitting_grd                         true
% 2.89/0.99  --splitting_cvd                         false
% 2.89/0.99  --splitting_cvd_svl                     false
% 2.89/0.99  --splitting_nvd                         32
% 2.89/0.99  --sub_typing                            true
% 2.89/0.99  --prep_gs_sim                           true
% 2.89/0.99  --prep_unflatten                        true
% 2.89/0.99  --prep_res_sim                          true
% 2.89/0.99  --prep_upred                            true
% 2.89/0.99  --prep_sem_filter                       exhaustive
% 2.89/0.99  --prep_sem_filter_out                   false
% 2.89/0.99  --pred_elim                             true
% 2.89/0.99  --res_sim_input                         true
% 2.89/0.99  --eq_ax_congr_red                       true
% 2.89/0.99  --pure_diseq_elim                       true
% 2.89/0.99  --brand_transform                       false
% 2.89/0.99  --non_eq_to_eq                          false
% 2.89/0.99  --prep_def_merge                        true
% 2.89/0.99  --prep_def_merge_prop_impl              false
% 2.89/0.99  --prep_def_merge_mbd                    true
% 2.89/0.99  --prep_def_merge_tr_red                 false
% 2.89/0.99  --prep_def_merge_tr_cl                  false
% 2.89/0.99  --smt_preprocessing                     true
% 2.89/0.99  --smt_ac_axioms                         fast
% 2.89/0.99  --preprocessed_out                      false
% 2.89/0.99  --preprocessed_stats                    false
% 2.89/0.99  
% 2.89/0.99  ------ Abstraction refinement Options
% 2.89/0.99  
% 2.89/0.99  --abstr_ref                             []
% 2.89/0.99  --abstr_ref_prep                        false
% 2.89/0.99  --abstr_ref_until_sat                   false
% 2.89/0.99  --abstr_ref_sig_restrict                funpre
% 2.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.99  --abstr_ref_under                       []
% 2.89/0.99  
% 2.89/0.99  ------ SAT Options
% 2.89/0.99  
% 2.89/0.99  --sat_mode                              false
% 2.89/0.99  --sat_fm_restart_options                ""
% 2.89/0.99  --sat_gr_def                            false
% 2.89/0.99  --sat_epr_types                         true
% 2.89/0.99  --sat_non_cyclic_types                  false
% 2.89/0.99  --sat_finite_models                     false
% 2.89/0.99  --sat_fm_lemmas                         false
% 2.89/0.99  --sat_fm_prep                           false
% 2.89/0.99  --sat_fm_uc_incr                        true
% 2.89/0.99  --sat_out_model                         small
% 2.89/0.99  --sat_out_clauses                       false
% 2.89/0.99  
% 2.89/0.99  ------ QBF Options
% 2.89/0.99  
% 2.89/0.99  --qbf_mode                              false
% 2.89/0.99  --qbf_elim_univ                         false
% 2.89/0.99  --qbf_dom_inst                          none
% 2.89/0.99  --qbf_dom_pre_inst                      false
% 2.89/0.99  --qbf_sk_in                             false
% 2.89/0.99  --qbf_pred_elim                         true
% 2.89/0.99  --qbf_split                             512
% 2.89/0.99  
% 2.89/0.99  ------ BMC1 Options
% 2.89/0.99  
% 2.89/0.99  --bmc1_incremental                      false
% 2.89/0.99  --bmc1_axioms                           reachable_all
% 2.89/0.99  --bmc1_min_bound                        0
% 2.89/0.99  --bmc1_max_bound                        -1
% 2.89/0.99  --bmc1_max_bound_default                -1
% 2.89/0.99  --bmc1_symbol_reachability              true
% 2.89/0.99  --bmc1_property_lemmas                  false
% 2.89/0.99  --bmc1_k_induction                      false
% 2.89/0.99  --bmc1_non_equiv_states                 false
% 2.89/0.99  --bmc1_deadlock                         false
% 2.89/0.99  --bmc1_ucm                              false
% 2.89/0.99  --bmc1_add_unsat_core                   none
% 2.89/0.99  --bmc1_unsat_core_children              false
% 2.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.99  --bmc1_out_stat                         full
% 2.89/0.99  --bmc1_ground_init                      false
% 2.89/0.99  --bmc1_pre_inst_next_state              false
% 2.89/0.99  --bmc1_pre_inst_state                   false
% 2.89/0.99  --bmc1_pre_inst_reach_state             false
% 2.89/0.99  --bmc1_out_unsat_core                   false
% 2.89/0.99  --bmc1_aig_witness_out                  false
% 2.89/0.99  --bmc1_verbose                          false
% 2.89/0.99  --bmc1_dump_clauses_tptp                false
% 2.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.99  --bmc1_dump_file                        -
% 2.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.99  --bmc1_ucm_extend_mode                  1
% 2.89/0.99  --bmc1_ucm_init_mode                    2
% 2.89/0.99  --bmc1_ucm_cone_mode                    none
% 2.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.99  --bmc1_ucm_relax_model                  4
% 2.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.99  --bmc1_ucm_layered_model                none
% 2.89/0.99  --bmc1_ucm_max_lemma_size               10
% 2.89/0.99  
% 2.89/0.99  ------ AIG Options
% 2.89/0.99  
% 2.89/0.99  --aig_mode                              false
% 2.89/0.99  
% 2.89/0.99  ------ Instantiation Options
% 2.89/0.99  
% 2.89/0.99  --instantiation_flag                    true
% 2.89/0.99  --inst_sos_flag                         false
% 2.89/0.99  --inst_sos_phase                        true
% 2.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.99  --inst_lit_sel_side                     none
% 2.89/0.99  --inst_solver_per_active                1400
% 2.89/0.99  --inst_solver_calls_frac                1.
% 2.89/0.99  --inst_passive_queue_type               priority_queues
% 2.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.99  --inst_passive_queues_freq              [25;2]
% 2.89/0.99  --inst_dismatching                      true
% 2.89/0.99  --inst_eager_unprocessed_to_passive     true
% 2.89/0.99  --inst_prop_sim_given                   true
% 2.89/0.99  --inst_prop_sim_new                     false
% 2.89/0.99  --inst_subs_new                         false
% 2.89/0.99  --inst_eq_res_simp                      false
% 2.89/0.99  --inst_subs_given                       false
% 2.89/0.99  --inst_orphan_elimination               true
% 2.89/0.99  --inst_learning_loop_flag               true
% 2.89/0.99  --inst_learning_start                   3000
% 2.89/0.99  --inst_learning_factor                  2
% 2.89/0.99  --inst_start_prop_sim_after_learn       3
% 2.89/0.99  --inst_sel_renew                        solver
% 2.89/0.99  --inst_lit_activity_flag                true
% 2.89/0.99  --inst_restr_to_given                   false
% 2.89/0.99  --inst_activity_threshold               500
% 2.89/0.99  --inst_out_proof                        true
% 2.89/0.99  
% 2.89/0.99  ------ Resolution Options
% 2.89/0.99  
% 2.89/0.99  --resolution_flag                       false
% 2.89/0.99  --res_lit_sel                           adaptive
% 2.89/0.99  --res_lit_sel_side                      none
% 2.89/0.99  --res_ordering                          kbo
% 2.89/0.99  --res_to_prop_solver                    active
% 2.89/0.99  --res_prop_simpl_new                    false
% 2.89/0.99  --res_prop_simpl_given                  true
% 2.89/0.99  --res_passive_queue_type                priority_queues
% 2.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.99  --res_passive_queues_freq               [15;5]
% 2.89/0.99  --res_forward_subs                      full
% 2.89/0.99  --res_backward_subs                     full
% 2.89/0.99  --res_forward_subs_resolution           true
% 2.89/0.99  --res_backward_subs_resolution          true
% 2.89/0.99  --res_orphan_elimination                true
% 2.89/0.99  --res_time_limit                        2.
% 2.89/0.99  --res_out_proof                         true
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Options
% 2.89/0.99  
% 2.89/0.99  --superposition_flag                    true
% 2.89/0.99  --sup_passive_queue_type                priority_queues
% 2.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.99  --demod_completeness_check              fast
% 2.89/0.99  --demod_use_ground                      true
% 2.89/0.99  --sup_to_prop_solver                    passive
% 2.89/0.99  --sup_prop_simpl_new                    true
% 2.89/0.99  --sup_prop_simpl_given                  true
% 2.89/0.99  --sup_fun_splitting                     false
% 2.89/0.99  --sup_smt_interval                      50000
% 2.89/0.99  
% 2.89/0.99  ------ Superposition Simplification Setup
% 2.89/0.99  
% 2.89/0.99  --sup_indices_passive                   []
% 2.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_full_bw                           [BwDemod]
% 2.89/0.99  --sup_immed_triv                        [TrivRules]
% 2.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_immed_bw_main                     []
% 2.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.99  
% 2.89/0.99  ------ Combination Options
% 2.89/0.99  
% 2.89/0.99  --comb_res_mult                         3
% 2.89/0.99  --comb_sup_mult                         2
% 2.89/0.99  --comb_inst_mult                        10
% 2.89/0.99  
% 2.89/0.99  ------ Debug Options
% 2.89/0.99  
% 2.89/0.99  --dbg_backtrace                         false
% 2.89/0.99  --dbg_dump_prop_clauses                 false
% 2.89/0.99  --dbg_dump_prop_clauses_file            -
% 2.89/0.99  --dbg_out_stat                          false
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  ------ Proving...
% 2.89/0.99  
% 2.89/0.99  
% 2.89/0.99  % SZS status Theorem for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/0.99  
% 2.89/0.99  fof(f5,axiom,(
% 2.89/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f49,plain,(
% 2.89/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/0.99    inference(nnf_transformation,[],[f5])).
% 2.89/0.99  
% 2.89/0.99  fof(f50,plain,(
% 2.89/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.89/0.99    inference(flattening,[],[f49])).
% 2.89/0.99  
% 2.89/0.99  fof(f71,plain,(
% 2.89/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.89/0.99    inference(cnf_transformation,[],[f50])).
% 2.89/0.99  
% 2.89/0.99  fof(f114,plain,(
% 2.89/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.89/0.99    inference(equality_resolution,[],[f71])).
% 2.89/0.99  
% 2.89/0.99  fof(f17,axiom,(
% 2.89/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f26,plain,(
% 2.89/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.89/0.99    inference(pure_predicate_removal,[],[f17])).
% 2.89/0.99  
% 2.89/0.99  fof(f97,plain,(
% 2.89/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f26])).
% 2.89/0.99  
% 2.89/0.99  fof(f6,axiom,(
% 2.89/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f51,plain,(
% 2.89/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.89/0.99    inference(nnf_transformation,[],[f6])).
% 2.89/0.99  
% 2.89/0.99  fof(f72,plain,(
% 2.89/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f51])).
% 2.89/0.99  
% 2.89/0.99  fof(f4,axiom,(
% 2.89/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f29,plain,(
% 2.89/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.89/0.99    inference(ennf_transformation,[],[f4])).
% 2.89/0.99  
% 2.89/0.99  fof(f68,plain,(
% 2.89/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f29])).
% 2.89/0.99  
% 2.89/0.99  fof(f70,plain,(
% 2.89/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.89/0.99    inference(cnf_transformation,[],[f50])).
% 2.89/0.99  
% 2.89/0.99  fof(f115,plain,(
% 2.89/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.89/0.99    inference(equality_resolution,[],[f70])).
% 2.89/0.99  
% 2.89/0.99  fof(f14,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f37,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f14])).
% 2.89/0.99  
% 2.89/0.99  fof(f89,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f37])).
% 2.89/0.99  
% 2.89/0.99  fof(f8,axiom,(
% 2.89/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f78,plain,(
% 2.89/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.89/0.99    inference(cnf_transformation,[],[f8])).
% 2.89/0.99  
% 2.89/0.99  fof(f16,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f39,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f16])).
% 2.89/0.99  
% 2.89/0.99  fof(f40,plain,(
% 2.89/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(flattening,[],[f39])).
% 2.89/0.99  
% 2.89/0.99  fof(f58,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(nnf_transformation,[],[f40])).
% 2.89/0.99  
% 2.89/0.99  fof(f91,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f58])).
% 2.89/0.99  
% 2.89/0.99  fof(f21,conjecture,(
% 2.89/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f22,negated_conjecture,(
% 2.89/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.89/0.99    inference(negated_conjecture,[],[f21])).
% 2.89/0.99  
% 2.89/0.99  fof(f43,plain,(
% 2.89/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.89/0.99    inference(ennf_transformation,[],[f22])).
% 2.89/0.99  
% 2.89/0.99  fof(f44,plain,(
% 2.89/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.89/0.99    inference(flattening,[],[f43])).
% 2.89/0.99  
% 2.89/0.99  fof(f61,plain,(
% 2.89/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))) & k2_relset_1(sK5,sK6,sK7) = sK6 & v2_funct_1(sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 2.89/0.99    introduced(choice_axiom,[])).
% 2.89/0.99  
% 2.89/0.99  fof(f62,plain,(
% 2.89/0.99    (~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))) & k2_relset_1(sK5,sK6,sK7) = sK6 & v2_funct_1(sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 2.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f44,f61])).
% 2.89/0.99  
% 2.89/0.99  fof(f107,plain,(
% 2.89/0.99    v1_funct_2(sK7,sK5,sK6)),
% 2.89/0.99    inference(cnf_transformation,[],[f62])).
% 2.89/0.99  
% 2.89/0.99  fof(f108,plain,(
% 2.89/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 2.89/0.99    inference(cnf_transformation,[],[f62])).
% 2.89/0.99  
% 2.89/0.99  fof(f13,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f36,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f13])).
% 2.89/0.99  
% 2.89/0.99  fof(f88,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f36])).
% 2.89/0.99  
% 2.89/0.99  fof(f12,axiom,(
% 2.89/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f34,plain,(
% 2.89/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.89/0.99    inference(ennf_transformation,[],[f12])).
% 2.89/0.99  
% 2.89/0.99  fof(f35,plain,(
% 2.89/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/0.99    inference(flattening,[],[f34])).
% 2.89/0.99  
% 2.89/0.99  fof(f87,plain,(
% 2.89/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f35])).
% 2.89/0.99  
% 2.89/0.99  fof(f109,plain,(
% 2.89/0.99    v2_funct_1(sK7)),
% 2.89/0.99    inference(cnf_transformation,[],[f62])).
% 2.89/0.99  
% 2.89/0.99  fof(f106,plain,(
% 2.89/0.99    v1_funct_1(sK7)),
% 2.89/0.99    inference(cnf_transformation,[],[f62])).
% 2.89/0.99  
% 2.89/0.99  fof(f20,axiom,(
% 2.89/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f41,plain,(
% 2.89/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.89/0.99    inference(ennf_transformation,[],[f20])).
% 2.89/0.99  
% 2.89/0.99  fof(f42,plain,(
% 2.89/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/0.99    inference(flattening,[],[f41])).
% 2.89/0.99  
% 2.89/0.99  fof(f105,plain,(
% 2.89/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f42])).
% 2.89/0.99  
% 2.89/0.99  fof(f15,axiom,(
% 2.89/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f38,plain,(
% 2.89/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.89/0.99    inference(ennf_transformation,[],[f15])).
% 2.89/0.99  
% 2.89/0.99  fof(f90,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f38])).
% 2.89/0.99  
% 2.89/0.99  fof(f110,plain,(
% 2.89/0.99    k2_relset_1(sK5,sK6,sK7) = sK6),
% 2.89/0.99    inference(cnf_transformation,[],[f62])).
% 2.89/0.99  
% 2.89/0.99  fof(f86,plain,(
% 2.89/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f35])).
% 2.89/0.99  
% 2.89/0.99  fof(f10,axiom,(
% 2.89/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f32,plain,(
% 2.89/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.89/0.99    inference(ennf_transformation,[],[f10])).
% 2.89/0.99  
% 2.89/0.99  fof(f33,plain,(
% 2.89/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.89/0.99    inference(flattening,[],[f32])).
% 2.89/0.99  
% 2.89/0.99  fof(f83,plain,(
% 2.89/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f33])).
% 2.89/0.99  
% 2.89/0.99  fof(f82,plain,(
% 2.89/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f33])).
% 2.89/0.99  
% 2.89/0.99  fof(f104,plain,(
% 2.89/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f42])).
% 2.89/0.99  
% 2.89/0.99  fof(f111,plain,(
% 2.89/0.99    ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))),
% 2.89/0.99    inference(cnf_transformation,[],[f62])).
% 2.89/0.99  
% 2.89/0.99  fof(f9,axiom,(
% 2.89/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f30,plain,(
% 2.89/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.89/0.99    inference(ennf_transformation,[],[f9])).
% 2.89/0.99  
% 2.89/0.99  fof(f31,plain,(
% 2.89/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.89/0.99    inference(flattening,[],[f30])).
% 2.89/0.99  
% 2.89/0.99  fof(f80,plain,(
% 2.89/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f31])).
% 2.89/0.99  
% 2.89/0.99  fof(f81,plain,(
% 2.89/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f31])).
% 2.89/0.99  
% 2.89/0.99  fof(f94,plain,(
% 2.89/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f58])).
% 2.89/0.99  
% 2.89/0.99  fof(f121,plain,(
% 2.89/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.89/0.99    inference(equality_resolution,[],[f94])).
% 2.89/0.99  
% 2.89/0.99  fof(f11,axiom,(
% 2.89/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f84,plain,(
% 2.89/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f11])).
% 2.89/0.99  
% 2.89/0.99  fof(f19,axiom,(
% 2.89/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.89/0.99  
% 2.89/0.99  fof(f102,plain,(
% 2.89/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f19])).
% 2.89/0.99  
% 2.89/0.99  fof(f113,plain,(
% 2.89/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.89/0.99    inference(definition_unfolding,[],[f84,f102])).
% 2.89/0.99  
% 2.89/0.99  fof(f85,plain,(
% 2.89/0.99    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.89/0.99    inference(cnf_transformation,[],[f11])).
% 2.89/0.99  
% 2.89/0.99  fof(f112,plain,(
% 2.89/0.99    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.89/0.99    inference(definition_unfolding,[],[f85,f102])).
% 2.89/0.99  
% 2.89/0.99  fof(f79,plain,(
% 2.89/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.89/0.99    inference(cnf_transformation,[],[f8])).
% 2.89/0.99  
% 2.89/0.99  fof(f69,plain,(
% 2.89/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.89/0.99    inference(cnf_transformation,[],[f50])).
% 2.89/0.99  
% 2.89/0.99  cnf(c_6,plain,
% 2.89/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f114]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_34,plain,
% 2.89/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1915,plain,
% 2.89/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2790,plain,
% 2.89/0.99      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_6,c_1915]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_10,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.89/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1929,plain,
% 2.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.89/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_2998,plain,
% 2.89/0.99      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_2790,c_1929]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_5,plain,
% 2.89/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1931,plain,
% 2.89/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3239,plain,
% 2.89/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_2998,c_1931]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3242,plain,
% 2.89/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.89/0.99      inference(demodulation,[status(thm)],[c_3239,c_2790]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_7,plain,
% 2.89/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f115]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_26,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1917,plain,
% 2.89/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.89/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3774,plain,
% 2.89/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_7,c_1917]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4924,plain,
% 2.89/0.99      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_3242,c_3774]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_16,plain,
% 2.89/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.89/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_4932,plain,
% 2.89/0.99      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 2.89/0.99      inference(light_normalisation,[status(thm)],[c_4924,c_16]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_33,plain,
% 2.89/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.89/0.99      | k1_xboole_0 = X2 ),
% 2.89/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_46,negated_conjecture,
% 2.89/0.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 2.89/0.99      inference(cnf_transformation,[],[f107]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_893,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.89/0.99      | sK5 != X1
% 2.89/0.99      | sK6 != X2
% 2.89/0.99      | sK7 != X0
% 2.89/0.99      | k1_xboole_0 = X2 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_46]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_894,plain,
% 2.89/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.89/0.99      | k1_relset_1(sK5,sK6,sK7) = sK5
% 2.89/0.99      | k1_xboole_0 = sK6 ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_893]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_45,negated_conjecture,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 2.89/0.99      inference(cnf_transformation,[],[f108]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_896,plain,
% 2.89/0.99      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_894,c_45]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1910,plain,
% 2.89/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3771,plain,
% 2.89/0.99      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1910,c_1917]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3928,plain,
% 2.89/0.99      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_896,c_3771]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_25,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | v1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1918,plain,
% 2.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.89/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3477,plain,
% 2.89/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1910,c_1918]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_23,plain,
% 2.89/0.99      ( ~ v2_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_relat_1(X0)
% 2.89/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_44,negated_conjecture,
% 2.89/0.99      ( v2_funct_1(sK7) ),
% 2.89/0.99      inference(cnf_transformation,[],[f109]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_579,plain,
% 2.89/0.99      ( ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_relat_1(X0)
% 2.89/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.89/0.99      | sK7 != X0 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_44]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_580,plain,
% 2.89/0.99      ( ~ v1_funct_1(sK7)
% 2.89/0.99      | ~ v1_relat_1(sK7)
% 2.89/0.99      | k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7) ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_579]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_47,negated_conjecture,
% 2.89/0.99      ( v1_funct_1(sK7) ),
% 2.89/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_582,plain,
% 2.89/0.99      ( ~ v1_relat_1(sK7)
% 2.89/0.99      | k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_580,c_47]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1906,plain,
% 2.89/0.99      ( k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7)
% 2.89/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3592,plain,
% 2.89/0.99      ( k2_relat_1(k2_funct_1(sK7)) = k1_relat_1(sK7) ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_3477,c_1906]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_39,plain,
% 2.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1911,plain,
% 2.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.89/0.99      | v1_funct_1(X0) != iProver_top
% 2.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3691,plain,
% 2.89/0.99      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k1_relat_1(sK7)))) = iProver_top
% 2.89/0.99      | v1_funct_1(k2_funct_1(sK7)) != iProver_top
% 2.89/0.99      | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_3592,c_1911]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_27,plain,
% 2.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.89/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1916,plain,
% 2.89/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.89/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.89/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3406,plain,
% 2.89/0.99      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 2.89/0.99      inference(superposition,[status(thm)],[c_1910,c_1916]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_43,negated_conjecture,
% 2.89/0.99      ( k2_relset_1(sK5,sK6,sK7) = sK6 ),
% 2.89/0.99      inference(cnf_transformation,[],[f110]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_3418,plain,
% 2.89/0.99      ( k2_relat_1(sK7) = sK6 ),
% 2.89/0.99      inference(light_normalisation,[status(thm)],[c_3406,c_43]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_24,plain,
% 2.89/0.99      ( ~ v2_funct_1(X0)
% 2.89/0.99      | ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_relat_1(X0)
% 2.89/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.89/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_565,plain,
% 2.89/0.99      ( ~ v1_funct_1(X0)
% 2.89/0.99      | ~ v1_relat_1(X0)
% 2.89/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.89/0.99      | sK7 != X0 ),
% 2.89/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_44]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_566,plain,
% 2.89/0.99      ( ~ v1_funct_1(sK7)
% 2.89/0.99      | ~ v1_relat_1(sK7)
% 2.89/0.99      | k1_relat_1(k2_funct_1(sK7)) = k2_relat_1(sK7) ),
% 2.89/0.99      inference(unflattening,[status(thm)],[c_565]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_568,plain,
% 2.89/0.99      ( ~ v1_relat_1(sK7)
% 2.89/0.99      | k1_relat_1(k2_funct_1(sK7)) = k2_relat_1(sK7) ),
% 2.89/0.99      inference(global_propositional_subsumption,
% 2.89/0.99                [status(thm)],
% 2.89/0.99                [c_566,c_47]) ).
% 2.89/0.99  
% 2.89/0.99  cnf(c_1907,plain,
% 2.89/0.99      ( k1_relat_1(k2_funct_1(sK7)) = k2_relat_1(sK7)
% 2.89/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3460,plain,
% 2.89/1.00      ( k1_relat_1(k2_funct_1(sK7)) = sK6
% 2.89/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_3418,c_1907]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_50,plain,
% 2.89/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2296,plain,
% 2.89/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.89/1.00      | v1_relat_1(sK7) ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2297,plain,
% 2.89/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 2.89/1.00      | v1_relat_1(sK7) = iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_2296]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3662,plain,
% 2.89/1.00      ( k1_relat_1(k2_funct_1(sK7)) = sK6 ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_3460,c_50,c_2297]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3692,plain,
% 2.89/1.00      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7)))) = iProver_top
% 2.89/1.00      | v1_funct_1(k2_funct_1(sK7)) != iProver_top
% 2.89/1.00      | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
% 2.89/1.00      inference(light_normalisation,[status(thm)],[c_3691,c_3662]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_48,plain,
% 2.89/1.00      ( v1_funct_1(sK7) = iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_19,plain,
% 2.89/1.00      ( ~ v1_funct_1(X0)
% 2.89/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.89/1.00      | ~ v1_relat_1(X0) ),
% 2.89/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2268,plain,
% 2.89/1.00      ( v1_funct_1(k2_funct_1(sK7))
% 2.89/1.00      | ~ v1_funct_1(sK7)
% 2.89/1.00      | ~ v1_relat_1(sK7) ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2269,plain,
% 2.89/1.00      ( v1_funct_1(k2_funct_1(sK7)) = iProver_top
% 2.89/1.00      | v1_funct_1(sK7) != iProver_top
% 2.89/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_20,plain,
% 2.89/1.00      ( ~ v1_funct_1(X0)
% 2.89/1.00      | ~ v1_relat_1(X0)
% 2.89/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 2.89/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2281,plain,
% 2.89/1.00      ( ~ v1_funct_1(sK7)
% 2.89/1.00      | v1_relat_1(k2_funct_1(sK7))
% 2.89/1.00      | ~ v1_relat_1(sK7) ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2282,plain,
% 2.89/1.00      ( v1_funct_1(sK7) != iProver_top
% 2.89/1.00      | v1_relat_1(k2_funct_1(sK7)) = iProver_top
% 2.89/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_2281]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4205,plain,
% 2.89/1.00      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7)))) = iProver_top ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_3692,c_48,c_50,c_2269,c_2282,c_2297]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4213,plain,
% 2.89/1.00      ( k1_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = k1_relat_1(k2_funct_1(sK7)) ),
% 2.89/1.00      inference(superposition,[status(thm)],[c_4205,c_1917]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4219,plain,
% 2.89/1.00      ( k1_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = sK6 ),
% 2.89/1.00      inference(light_normalisation,[status(thm)],[c_4213,c_3662]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4233,plain,
% 2.89/1.00      ( k1_relset_1(sK6,sK5,k2_funct_1(sK7)) = sK6 | sK6 = k1_xboole_0 ),
% 2.89/1.00      inference(superposition,[status(thm)],[c_3928,c_4219]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_40,plain,
% 2.89/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.89/1.00      | ~ v1_funct_1(X0)
% 2.89/1.00      | ~ v1_relat_1(X0) ),
% 2.89/1.00      inference(cnf_transformation,[],[f104]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_42,negated_conjecture,
% 2.89/1.00      ( ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
% 2.89/1.00      | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.89/1.00      | ~ v1_funct_1(k2_funct_1(sK7)) ),
% 2.89/1.00      inference(cnf_transformation,[],[f111]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_917,plain,
% 2.89/1.00      ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.89/1.00      | ~ v1_funct_1(X0)
% 2.89/1.00      | ~ v1_funct_1(k2_funct_1(sK7))
% 2.89/1.00      | ~ v1_relat_1(X0)
% 2.89/1.00      | k2_funct_1(sK7) != X0
% 2.89/1.00      | k1_relat_1(X0) != sK6
% 2.89/1.00      | k2_relat_1(X0) != sK5 ),
% 2.89/1.00      inference(resolution_lifted,[status(thm)],[c_40,c_42]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_918,plain,
% 2.89/1.00      ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.89/1.00      | ~ v1_funct_1(k2_funct_1(sK7))
% 2.89/1.00      | ~ v1_relat_1(k2_funct_1(sK7))
% 2.89/1.00      | k1_relat_1(k2_funct_1(sK7)) != sK6
% 2.89/1.00      | k2_relat_1(k2_funct_1(sK7)) != sK5 ),
% 2.89/1.00      inference(unflattening,[status(thm)],[c_917]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_930,plain,
% 2.89/1.00      ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.89/1.00      | ~ v1_funct_1(k2_funct_1(sK7))
% 2.89/1.00      | k1_relat_1(k2_funct_1(sK7)) != sK6
% 2.89/1.00      | k2_relat_1(k2_funct_1(sK7)) != sK5 ),
% 2.89/1.00      inference(forward_subsumption_resolution,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_918,c_25]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_1897,plain,
% 2.89/1.00      ( k1_relat_1(k2_funct_1(sK7)) != sK6
% 2.89/1.00      | k2_relat_1(k2_funct_1(sK7)) != sK5
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.89/1.00      | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_919,plain,
% 2.89/1.00      ( k1_relat_1(k2_funct_1(sK7)) != sK6
% 2.89/1.00      | k2_relat_1(k2_funct_1(sK7)) != sK5
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.89/1.00      | v1_funct_1(k2_funct_1(sK7)) != iProver_top
% 2.89/1.00      | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2410,plain,
% 2.89/1.00      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.89/1.00      | k2_relat_1(k2_funct_1(sK7)) != sK5
% 2.89/1.00      | k1_relat_1(k2_funct_1(sK7)) != sK6 ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_1897,c_48,c_50,c_919,c_2269,c_2282,c_2297]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2411,plain,
% 2.89/1.00      ( k1_relat_1(k2_funct_1(sK7)) != sK6
% 2.89/1.00      | k2_relat_1(k2_funct_1(sK7)) != sK5
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.89/1.00      inference(renaming,[status(thm)],[c_2410]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3665,plain,
% 2.89/1.00      ( k2_relat_1(k2_funct_1(sK7)) != sK5
% 2.89/1.00      | sK6 != sK6
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_3662,c_2411]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3712,plain,
% 2.89/1.00      ( k2_relat_1(k2_funct_1(sK7)) != sK5
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.89/1.00      inference(equality_resolution_simp,[status(thm)],[c_3665]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3714,plain,
% 2.89/1.00      ( k1_relat_1(sK7) != sK5
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.89/1.00      inference(light_normalisation,[status(thm)],[c_3712,c_3592]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4009,plain,
% 2.89/1.00      ( sK6 = k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.89/1.00      inference(superposition,[status(thm)],[c_3928,c_3714]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4210,plain,
% 2.89/1.00      ( sK6 = k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.89/1.00      inference(superposition,[status(thm)],[c_3928,c_4205]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4479,plain,
% 2.89/1.00      ( sK6 = k1_xboole_0 ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_4233,c_4009,c_4210]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_18,plain,
% 2.89/1.00      ( ~ v1_relat_1(X0)
% 2.89/1.00      | k1_relat_1(X0) != k1_xboole_0
% 2.89/1.00      | k1_xboole_0 = X0 ),
% 2.89/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_1923,plain,
% 2.89/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 2.89/1.00      | k1_xboole_0 = X0
% 2.89/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3816,plain,
% 2.89/1.00      ( k2_funct_1(sK7) = k1_xboole_0
% 2.89/1.00      | sK6 != k1_xboole_0
% 2.89/1.00      | v1_relat_1(k2_funct_1(sK7)) != iProver_top ),
% 2.89/1.00      inference(superposition,[status(thm)],[c_3662,c_1923]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4124,plain,
% 2.89/1.00      ( sK6 != k1_xboole_0 | k2_funct_1(sK7) = k1_xboole_0 ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_3816,c_48,c_50,c_2282,c_2297]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4125,plain,
% 2.89/1.00      ( k2_funct_1(sK7) = k1_xboole_0 | sK6 != k1_xboole_0 ),
% 2.89/1.00      inference(renaming,[status(thm)],[c_4124]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4484,plain,
% 2.89/1.00      ( k2_funct_1(sK7) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_4479,c_4125]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4621,plain,
% 2.89/1.00      ( k2_funct_1(sK7) = k1_xboole_0 ),
% 2.89/1.00      inference(equality_resolution_simp,[status(thm)],[c_4484]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_17,plain,
% 2.89/1.00      ( ~ v1_relat_1(X0)
% 2.89/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.89/1.00      | k1_xboole_0 = X0 ),
% 2.89/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_1924,plain,
% 2.89/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 2.89/1.00      | k1_xboole_0 = X0
% 2.89/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3849,plain,
% 2.89/1.00      ( sK6 != k1_xboole_0
% 2.89/1.00      | sK7 = k1_xboole_0
% 2.89/1.00      | v1_relat_1(sK7) != iProver_top ),
% 2.89/1.00      inference(superposition,[status(thm)],[c_3418,c_1924]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3863,plain,
% 2.89/1.00      ( ~ v1_relat_1(sK7) | sK6 != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.89/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3849]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4001,plain,
% 2.89/1.00      ( sK7 = k1_xboole_0 | sK6 != k1_xboole_0 ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_3849,c_45,c_2296,c_3863]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4002,plain,
% 2.89/1.00      ( sK6 != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.89/1.00      inference(renaming,[status(thm)],[c_4001]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4485,plain,
% 2.89/1.00      ( sK7 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_4479,c_4002]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4571,plain,
% 2.89/1.00      ( sK7 = k1_xboole_0 ),
% 2.89/1.00      inference(equality_resolution_simp,[status(thm)],[c_4485]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4622,plain,
% 2.89/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.89/1.00      inference(light_normalisation,[status(thm)],[c_4621,c_4571]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_30,plain,
% 2.89/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.89/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.89/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.89/1.00      inference(cnf_transformation,[],[f121]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_810,plain,
% 2.89/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.89/1.00      | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.89/1.00      | ~ v1_funct_1(k2_funct_1(sK7))
% 2.89/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.89/1.00      | k2_funct_1(sK7) != X0
% 2.89/1.00      | sK5 != X1
% 2.89/1.00      | sK6 != k1_xboole_0 ),
% 2.89/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_42]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_811,plain,
% 2.89/1.00      ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.89/1.00      | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 2.89/1.00      | ~ v1_funct_1(k2_funct_1(sK7))
% 2.89/1.00      | k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
% 2.89/1.00      | sK6 != k1_xboole_0 ),
% 2.89/1.00      inference(unflattening,[status(thm)],[c_810]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_1902,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
% 2.89/1.00      | sK6 != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
% 2.89/1.00      | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2142,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
% 2.89/1.00      | sK6 != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.89/1.00      | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_1902,c_7]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2488,plain,
% 2.89/1.00      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.89/1.00      | sK6 != k1_xboole_0
% 2.89/1.00      | k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0 ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_2142,c_48,c_50,c_2269,c_2297]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2489,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
% 2.89/1.00      | sK6 != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.00      inference(renaming,[status(thm)],[c_2488]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4497,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
% 2.89/1.00      | k1_xboole_0 != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_4479,c_2489]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4535,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.00      inference(equality_resolution_simp,[status(thm)],[c_4497]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4539,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(sK7)) != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_4535,c_7]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4580,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_4571,c_4539]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4626,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k1_xboole_0) != k1_xboole_0
% 2.89/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_4622,c_4580]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_22,plain,
% 2.89/1.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.89/1.00      inference(cnf_transformation,[],[f113]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_108,plain,
% 2.89/1.00      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_110,plain,
% 2.89/1.00      ( v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_108]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_21,plain,
% 2.89/1.00      ( v1_funct_1(k6_partfun1(X0)) ),
% 2.89/1.00      inference(cnf_transformation,[],[f112]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_111,plain,
% 2.89/1.00      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_113,plain,
% 2.89/1.00      ( v1_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_111]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_1020,plain,
% 2.89/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.89/1.00      theory(equality) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2300,plain,
% 2.89/1.00      ( v1_relat_1(X0)
% 2.89/1.00      | ~ v1_relat_1(k6_partfun1(X1))
% 2.89/1.00      | X0 != k6_partfun1(X1) ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_1020]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2301,plain,
% 2.89/1.00      ( X0 != k6_partfun1(X1)
% 2.89/1.00      | v1_relat_1(X0) = iProver_top
% 2.89/1.00      | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_2300]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2303,plain,
% 2.89/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 2.89/1.00      | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 2.89/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_2301]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_1022,plain,
% 2.89/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.89/1.00      theory(equality) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2325,plain,
% 2.89/1.00      ( v1_funct_1(X0)
% 2.89/1.00      | ~ v1_funct_1(k6_partfun1(X1))
% 2.89/1.00      | X0 != k6_partfun1(X1) ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_1022]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2326,plain,
% 2.89/1.00      ( X0 != k6_partfun1(X1)
% 2.89/1.00      | v1_funct_1(X0) = iProver_top
% 2.89/1.00      | v1_funct_1(k6_partfun1(X1)) != iProver_top ),
% 2.89/1.00      inference(predicate_to_equality,[status(thm)],[c_2325]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2328,plain,
% 2.89/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 2.89/1.00      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 2.89/1.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_2326]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_15,plain,
% 2.89/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.89/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2916,plain,
% 2.89/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
% 2.89/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.89/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.89/1.00      inference(superposition,[status(thm)],[c_15,c_1911]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2920,plain,
% 2.89/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 2.89/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.89/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.89/1.00      inference(light_normalisation,[status(thm)],[c_2916,c_16]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_2921,plain,
% 2.89/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.89/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.89/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_2920,c_7]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3029,plain,
% 2.89/1.00      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
% 2.89/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2998]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3075,plain,
% 2.89/1.00      ( ~ r1_tarski(k6_partfun1(X0),k1_xboole_0)
% 2.89/1.00      | k1_xboole_0 = k6_partfun1(X0) ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_3077,plain,
% 2.89/1.00      ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
% 2.89/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_3075]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4872,plain,
% 2.89/1.00      ( k1_relset_1(k1_xboole_0,sK5,k1_xboole_0) != k1_xboole_0 ),
% 2.89/1.00      inference(global_propositional_subsumption,
% 2.89/1.00                [status(thm)],
% 2.89/1.00                [c_4626,c_110,c_113,c_2303,c_2328,c_2921,c_3029,c_3077]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_4940,plain,
% 2.89/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.89/1.00      inference(demodulation,[status(thm)],[c_4932,c_4872]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_141,plain,
% 2.89/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_8,plain,
% 2.89/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.89/1.00      | k1_xboole_0 = X0
% 2.89/1.00      | k1_xboole_0 = X1 ),
% 2.89/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(c_140,plain,
% 2.89/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.89/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.89/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.89/1.00  
% 2.89/1.00  cnf(contradiction,plain,
% 2.89/1.00      ( $false ),
% 2.89/1.00      inference(minisat,[status(thm)],[c_4940,c_141,c_140]) ).
% 2.89/1.00  
% 2.89/1.00  
% 2.89/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/1.00  
% 2.89/1.00  ------                               Statistics
% 2.89/1.00  
% 2.89/1.00  ------ General
% 2.89/1.00  
% 2.89/1.00  abstr_ref_over_cycles:                  0
% 2.89/1.00  abstr_ref_under_cycles:                 0
% 2.89/1.00  gc_basic_clause_elim:                   0
% 2.89/1.00  forced_gc_time:                         0
% 2.89/1.00  parsing_time:                           0.01
% 2.89/1.00  unif_index_cands_time:                  0.
% 2.89/1.00  unif_index_add_time:                    0.
% 2.89/1.00  orderings_time:                         0.
% 2.89/1.00  out_proof_time:                         0.011
% 2.89/1.00  total_time:                             0.167
% 2.89/1.00  num_of_symbols:                         57
% 2.89/1.00  num_of_terms:                           3888
% 2.89/1.00  
% 2.89/1.00  ------ Preprocessing
% 2.89/1.00  
% 2.89/1.00  num_of_splits:                          0
% 2.89/1.00  num_of_split_atoms:                     0
% 2.89/1.00  num_of_reused_defs:                     0
% 2.89/1.00  num_eq_ax_congr_red:                    24
% 2.89/1.00  num_of_sem_filtered_clauses:            1
% 2.89/1.00  num_of_subtypes:                        0
% 2.89/1.00  monotx_restored_types:                  0
% 2.89/1.00  sat_num_of_epr_types:                   0
% 2.89/1.00  sat_num_of_non_cyclic_types:            0
% 2.89/1.00  sat_guarded_non_collapsed_types:        0
% 2.89/1.00  num_pure_diseq_elim:                    0
% 2.89/1.00  simp_replaced_by:                       0
% 2.89/1.00  res_preprocessed:                       178
% 2.89/1.00  prep_upred:                             0
% 2.89/1.00  prep_unflattend:                        61
% 2.89/1.00  smt_new_axioms:                         0
% 2.89/1.00  pred_elim_cands:                        8
% 2.89/1.00  pred_elim:                              3
% 2.89/1.00  pred_elim_cl:                           -2
% 2.89/1.00  pred_elim_cycles:                       5
% 2.89/1.00  merged_defs:                            6
% 2.89/1.00  merged_defs_ncl:                        0
% 2.89/1.00  bin_hyper_res:                          6
% 2.89/1.00  prep_cycles:                            3
% 2.89/1.00  pred_elim_time:                         0.01
% 2.89/1.00  splitting_time:                         0.
% 2.89/1.00  sem_filter_time:                        0.
% 2.89/1.00  monotx_time:                            0.013
% 2.89/1.00  subtype_inf_time:                       0.
% 2.89/1.00  
% 2.89/1.00  ------ Problem properties
% 2.89/1.00  
% 2.89/1.00  clauses:                                49
% 2.89/1.00  conjectures:                            3
% 2.89/1.00  epr:                                    4
% 2.89/1.00  horn:                                   41
% 2.89/1.00  ground:                                 16
% 2.89/1.00  unary:                                  15
% 2.89/1.00  binary:                                 15
% 2.89/1.00  lits:                                   113
% 2.89/1.00  lits_eq:                                47
% 2.89/1.00  fd_pure:                                0
% 2.89/1.00  fd_pseudo:                              0
% 2.89/1.00  fd_cond:                                5
% 2.89/1.00  fd_pseudo_cond:                         2
% 2.89/1.00  ac_symbols:                             0
% 2.89/1.00  
% 2.89/1.00  ------ Propositional Solver
% 2.89/1.00  
% 2.89/1.00  prop_solver_calls:                      23
% 2.89/1.00  prop_fast_solver_calls:                 1159
% 2.89/1.00  smt_solver_calls:                       0
% 2.89/1.00  smt_fast_solver_calls:                  0
% 2.89/1.00  prop_num_of_clauses:                    1538
% 2.89/1.00  prop_preprocess_simplified:             6126
% 2.89/1.00  prop_fo_subsumed:                       34
% 2.89/1.00  prop_solver_time:                       0.
% 2.89/1.00  smt_solver_time:                        0.
% 2.89/1.00  smt_fast_solver_time:                   0.
% 2.89/1.00  prop_fast_solver_time:                  0.
% 2.89/1.00  prop_unsat_core_time:                   0.
% 2.89/1.00  
% 2.89/1.00  ------ QBF
% 2.89/1.00  
% 2.89/1.00  qbf_q_res:                              0
% 2.89/1.00  qbf_num_tautologies:                    0
% 2.89/1.00  qbf_prep_cycles:                        0
% 2.89/1.00  
% 2.89/1.00  ------ BMC1
% 2.89/1.00  
% 2.89/1.00  bmc1_current_bound:                     -1
% 2.89/1.00  bmc1_last_solved_bound:                 -1
% 2.89/1.00  bmc1_unsat_core_size:                   -1
% 2.89/1.00  bmc1_unsat_core_parents_size:           -1
% 2.89/1.00  bmc1_merge_next_fun:                    0
% 2.89/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.89/1.00  
% 2.89/1.00  ------ Instantiation
% 2.89/1.00  
% 2.89/1.00  inst_num_of_clauses:                    531
% 2.89/1.00  inst_num_in_passive:                    135
% 2.89/1.00  inst_num_in_active:                     319
% 2.89/1.00  inst_num_in_unprocessed:                77
% 2.89/1.00  inst_num_of_loops:                      460
% 2.89/1.00  inst_num_of_learning_restarts:          0
% 2.89/1.00  inst_num_moves_active_passive:          138
% 2.89/1.00  inst_lit_activity:                      0
% 2.89/1.00  inst_lit_activity_moves:                0
% 2.89/1.00  inst_num_tautologies:                   0
% 2.89/1.00  inst_num_prop_implied:                  0
% 2.89/1.00  inst_num_existing_simplified:           0
% 2.89/1.00  inst_num_eq_res_simplified:             0
% 2.89/1.00  inst_num_child_elim:                    0
% 2.89/1.00  inst_num_of_dismatching_blockings:      118
% 2.89/1.00  inst_num_of_non_proper_insts:           369
% 2.89/1.00  inst_num_of_duplicates:                 0
% 2.89/1.00  inst_inst_num_from_inst_to_res:         0
% 2.89/1.00  inst_dismatching_checking_time:         0.
% 2.89/1.00  
% 2.89/1.00  ------ Resolution
% 2.89/1.00  
% 2.89/1.00  res_num_of_clauses:                     0
% 2.89/1.00  res_num_in_passive:                     0
% 2.89/1.00  res_num_in_active:                      0
% 2.89/1.00  res_num_of_loops:                       181
% 2.89/1.00  res_forward_subset_subsumed:            27
% 2.89/1.00  res_backward_subset_subsumed:           0
% 2.89/1.00  res_forward_subsumed:                   1
% 2.89/1.00  res_backward_subsumed:                  0
% 2.89/1.00  res_forward_subsumption_resolution:     4
% 2.89/1.00  res_backward_subsumption_resolution:    0
% 2.89/1.00  res_clause_to_clause_subsumption:       264
% 2.89/1.00  res_orphan_elimination:                 0
% 2.89/1.00  res_tautology_del:                      44
% 2.89/1.00  res_num_eq_res_simplified:              0
% 2.89/1.00  res_num_sel_changes:                    0
% 2.89/1.00  res_moves_from_active_to_pass:          0
% 2.89/1.00  
% 2.89/1.00  ------ Superposition
% 2.89/1.00  
% 2.89/1.00  sup_time_total:                         0.
% 2.89/1.00  sup_time_generating:                    0.
% 2.89/1.00  sup_time_sim_full:                      0.
% 2.89/1.00  sup_time_sim_immed:                     0.
% 2.89/1.00  
% 2.89/1.00  sup_num_of_clauses:                     96
% 2.89/1.00  sup_num_in_active:                      51
% 2.89/1.00  sup_num_in_passive:                     45
% 2.89/1.00  sup_num_of_loops:                       91
% 2.89/1.00  sup_fw_superposition:                   71
% 2.89/1.00  sup_bw_superposition:                   43
% 2.89/1.00  sup_immediate_simplified:               71
% 2.89/1.00  sup_given_eliminated:                   1
% 2.89/1.00  comparisons_done:                       0
% 2.89/1.00  comparisons_avoided:                    7
% 2.89/1.00  
% 2.89/1.00  ------ Simplifications
% 2.89/1.00  
% 2.89/1.00  
% 2.89/1.00  sim_fw_subset_subsumed:                 7
% 2.89/1.00  sim_bw_subset_subsumed:                 6
% 2.89/1.00  sim_fw_subsumed:                        10
% 2.89/1.00  sim_bw_subsumed:                        3
% 2.89/1.00  sim_fw_subsumption_res:                 2
% 2.89/1.00  sim_bw_subsumption_res:                 0
% 2.89/1.00  sim_tautology_del:                      3
% 2.89/1.00  sim_eq_tautology_del:                   9
% 2.89/1.00  sim_eq_res_simp:                        5
% 2.89/1.00  sim_fw_demodulated:                     20
% 2.89/1.00  sim_bw_demodulated:                     55
% 2.89/1.00  sim_light_normalised:                   30
% 2.89/1.00  sim_joinable_taut:                      0
% 2.89/1.00  sim_joinable_simp:                      0
% 2.89/1.00  sim_ac_normalised:                      0
% 2.89/1.00  sim_smt_subsumption:                    0
% 2.89/1.00  
%------------------------------------------------------------------------------
