%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:27 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  145 (2000 expanded)
%              Number of clauses        :   90 ( 613 expanded)
%              Number of leaves         :   13 ( 391 expanded)
%              Depth                    :   22
%              Number of atoms          :  473 (10905 expanded)
%              Number of equality atoms :  209 (2132 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f47])).

fof(f80,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_521,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_523,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_33])).

cnf(c_1450,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1453,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2756,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1450,c_1453])).

cnf(c_2808,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_523,c_2756])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_429,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_430,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_432,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_35])).

cnf(c_1446,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1713,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1727,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1446,c_35,c_33,c_430,c_1713])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1451,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2589,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_1451])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1452,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2387,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1450,c_1452])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2399,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2387,c_31])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_415,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_416,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_418,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_35])).

cnf(c_1447,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1731,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1447,c_35,c_33,c_416,c_1713])).

cnf(c_2506,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2399,c_1731])).

cnf(c_2601,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2589,c_2506])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1714,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1713])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1802,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1803,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1806,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1807,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1806])).

cnf(c_3382,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2601,c_36,c_38,c_1714,c_1803,c_1807])).

cnf(c_3389,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_3382,c_1453])).

cnf(c_3398,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3389,c_2506])).

cnf(c_3441,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2808,c_3398])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_679,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1
    | k2_funct_1(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_680,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_692,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_680,c_15])).

cnf(c_1434,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_681,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_1939,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1434,c_36,c_38,c_681,c_1714,c_1803,c_1807])).

cnf(c_1940,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1939])).

cnf(c_1943,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1940,c_1727,c_1731])).

cnf(c_2505,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2399,c_1943])).

cnf(c_2509,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2505])).

cnf(c_3162,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_2509])).

cnf(c_3387,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_3382])).

cnf(c_3561,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3441,c_3162,c_3387])).

cnf(c_3566,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3561,c_3382])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3640,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3566,c_3])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_346,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_347,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_376,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_347])).

cnf(c_377,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_377,c_30])).

cnf(c_627,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_960,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sP0_iProver_split
    | sK2 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_627])).

cnf(c_1437,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_1622,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1437,c_3])).

cnf(c_959,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_627])).

cnf(c_1438,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_1507,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1438,c_3])).

cnf(c_1628,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1622,c_1507])).

cnf(c_2060,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1628,c_36,c_38,c_1714,c_1803])).

cnf(c_2061,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2060])).

cnf(c_3574,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3561,c_2061])).

cnf(c_3619,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3574])).

cnf(c_3622,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3619,c_3])).

cnf(c_3642,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3640,c_3622])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.71/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/0.99  
% 2.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/0.99  
% 2.71/0.99  ------  iProver source info
% 2.71/0.99  
% 2.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/0.99  git: non_committed_changes: false
% 2.71/0.99  git: last_make_outside_of_git: false
% 2.71/0.99  
% 2.71/0.99  ------ 
% 2.71/0.99  
% 2.71/0.99  ------ Input Options
% 2.71/0.99  
% 2.71/0.99  --out_options                           all
% 2.71/0.99  --tptp_safe_out                         true
% 2.71/0.99  --problem_path                          ""
% 2.71/0.99  --include_path                          ""
% 2.71/0.99  --clausifier                            res/vclausify_rel
% 2.71/0.99  --clausifier_options                    --mode clausify
% 2.71/0.99  --stdin                                 false
% 2.71/0.99  --stats_out                             all
% 2.71/0.99  
% 2.71/0.99  ------ General Options
% 2.71/0.99  
% 2.71/0.99  --fof                                   false
% 2.71/0.99  --time_out_real                         305.
% 2.71/0.99  --time_out_virtual                      -1.
% 2.71/0.99  --symbol_type_check                     false
% 2.71/0.99  --clausify_out                          false
% 2.71/0.99  --sig_cnt_out                           false
% 2.71/0.99  --trig_cnt_out                          false
% 2.71/0.99  --trig_cnt_out_tolerance                1.
% 2.71/0.99  --trig_cnt_out_sk_spl                   false
% 2.71/0.99  --abstr_cl_out                          false
% 2.71/0.99  
% 2.71/0.99  ------ Global Options
% 2.71/0.99  
% 2.71/0.99  --schedule                              default
% 2.71/0.99  --add_important_lit                     false
% 2.71/0.99  --prop_solver_per_cl                    1000
% 2.71/0.99  --min_unsat_core                        false
% 2.71/0.99  --soft_assumptions                      false
% 2.71/0.99  --soft_lemma_size                       3
% 2.71/0.99  --prop_impl_unit_size                   0
% 2.71/0.99  --prop_impl_unit                        []
% 2.71/0.99  --share_sel_clauses                     true
% 2.71/0.99  --reset_solvers                         false
% 2.71/0.99  --bc_imp_inh                            [conj_cone]
% 2.71/0.99  --conj_cone_tolerance                   3.
% 2.71/0.99  --extra_neg_conj                        none
% 2.71/0.99  --large_theory_mode                     true
% 2.71/0.99  --prolific_symb_bound                   200
% 2.71/0.99  --lt_threshold                          2000
% 2.71/0.99  --clause_weak_htbl                      true
% 2.71/0.99  --gc_record_bc_elim                     false
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing Options
% 2.71/0.99  
% 2.71/0.99  --preprocessing_flag                    true
% 2.71/0.99  --time_out_prep_mult                    0.1
% 2.71/0.99  --splitting_mode                        input
% 2.71/0.99  --splitting_grd                         true
% 2.71/0.99  --splitting_cvd                         false
% 2.71/0.99  --splitting_cvd_svl                     false
% 2.71/0.99  --splitting_nvd                         32
% 2.71/0.99  --sub_typing                            true
% 2.71/0.99  --prep_gs_sim                           true
% 2.71/0.99  --prep_unflatten                        true
% 2.71/0.99  --prep_res_sim                          true
% 2.71/0.99  --prep_upred                            true
% 2.71/0.99  --prep_sem_filter                       exhaustive
% 2.71/0.99  --prep_sem_filter_out                   false
% 2.71/0.99  --pred_elim                             true
% 2.71/0.99  --res_sim_input                         true
% 2.71/0.99  --eq_ax_congr_red                       true
% 2.71/0.99  --pure_diseq_elim                       true
% 2.71/0.99  --brand_transform                       false
% 2.71/0.99  --non_eq_to_eq                          false
% 2.71/0.99  --prep_def_merge                        true
% 2.71/0.99  --prep_def_merge_prop_impl              false
% 2.71/0.99  --prep_def_merge_mbd                    true
% 2.71/0.99  --prep_def_merge_tr_red                 false
% 2.71/0.99  --prep_def_merge_tr_cl                  false
% 2.71/0.99  --smt_preprocessing                     true
% 2.71/0.99  --smt_ac_axioms                         fast
% 2.71/0.99  --preprocessed_out                      false
% 2.71/0.99  --preprocessed_stats                    false
% 2.71/0.99  
% 2.71/0.99  ------ Abstraction refinement Options
% 2.71/0.99  
% 2.71/0.99  --abstr_ref                             []
% 2.71/0.99  --abstr_ref_prep                        false
% 2.71/0.99  --abstr_ref_until_sat                   false
% 2.71/0.99  --abstr_ref_sig_restrict                funpre
% 2.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.99  --abstr_ref_under                       []
% 2.71/0.99  
% 2.71/0.99  ------ SAT Options
% 2.71/0.99  
% 2.71/0.99  --sat_mode                              false
% 2.71/0.99  --sat_fm_restart_options                ""
% 2.71/0.99  --sat_gr_def                            false
% 2.71/0.99  --sat_epr_types                         true
% 2.71/0.99  --sat_non_cyclic_types                  false
% 2.71/0.99  --sat_finite_models                     false
% 2.71/0.99  --sat_fm_lemmas                         false
% 2.71/0.99  --sat_fm_prep                           false
% 2.71/0.99  --sat_fm_uc_incr                        true
% 2.71/0.99  --sat_out_model                         small
% 2.71/0.99  --sat_out_clauses                       false
% 2.71/0.99  
% 2.71/0.99  ------ QBF Options
% 2.71/0.99  
% 2.71/0.99  --qbf_mode                              false
% 2.71/0.99  --qbf_elim_univ                         false
% 2.71/0.99  --qbf_dom_inst                          none
% 2.71/0.99  --qbf_dom_pre_inst                      false
% 2.71/0.99  --qbf_sk_in                             false
% 2.71/0.99  --qbf_pred_elim                         true
% 2.71/0.99  --qbf_split                             512
% 2.71/0.99  
% 2.71/0.99  ------ BMC1 Options
% 2.71/0.99  
% 2.71/0.99  --bmc1_incremental                      false
% 2.71/0.99  --bmc1_axioms                           reachable_all
% 2.71/0.99  --bmc1_min_bound                        0
% 2.71/0.99  --bmc1_max_bound                        -1
% 2.71/0.99  --bmc1_max_bound_default                -1
% 2.71/0.99  --bmc1_symbol_reachability              true
% 2.71/0.99  --bmc1_property_lemmas                  false
% 2.71/0.99  --bmc1_k_induction                      false
% 2.71/0.99  --bmc1_non_equiv_states                 false
% 2.71/0.99  --bmc1_deadlock                         false
% 2.71/0.99  --bmc1_ucm                              false
% 2.71/0.99  --bmc1_add_unsat_core                   none
% 2.71/0.99  --bmc1_unsat_core_children              false
% 2.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.99  --bmc1_out_stat                         full
% 2.71/0.99  --bmc1_ground_init                      false
% 2.71/0.99  --bmc1_pre_inst_next_state              false
% 2.71/0.99  --bmc1_pre_inst_state                   false
% 2.71/0.99  --bmc1_pre_inst_reach_state             false
% 2.71/0.99  --bmc1_out_unsat_core                   false
% 2.71/0.99  --bmc1_aig_witness_out                  false
% 2.71/0.99  --bmc1_verbose                          false
% 2.71/0.99  --bmc1_dump_clauses_tptp                false
% 2.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.99  --bmc1_dump_file                        -
% 2.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.99  --bmc1_ucm_extend_mode                  1
% 2.71/0.99  --bmc1_ucm_init_mode                    2
% 2.71/0.99  --bmc1_ucm_cone_mode                    none
% 2.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.99  --bmc1_ucm_relax_model                  4
% 2.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.99  --bmc1_ucm_layered_model                none
% 2.71/0.99  --bmc1_ucm_max_lemma_size               10
% 2.71/0.99  
% 2.71/0.99  ------ AIG Options
% 2.71/0.99  
% 2.71/0.99  --aig_mode                              false
% 2.71/0.99  
% 2.71/0.99  ------ Instantiation Options
% 2.71/0.99  
% 2.71/0.99  --instantiation_flag                    true
% 2.71/0.99  --inst_sos_flag                         false
% 2.71/0.99  --inst_sos_phase                        true
% 2.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.99  --inst_lit_sel_side                     num_symb
% 2.71/0.99  --inst_solver_per_active                1400
% 2.71/0.99  --inst_solver_calls_frac                1.
% 2.71/0.99  --inst_passive_queue_type               priority_queues
% 2.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.99  --inst_passive_queues_freq              [25;2]
% 2.71/0.99  --inst_dismatching                      true
% 2.71/0.99  --inst_eager_unprocessed_to_passive     true
% 2.71/0.99  --inst_prop_sim_given                   true
% 2.71/0.99  --inst_prop_sim_new                     false
% 2.71/0.99  --inst_subs_new                         false
% 2.71/0.99  --inst_eq_res_simp                      false
% 2.71/0.99  --inst_subs_given                       false
% 2.71/0.99  --inst_orphan_elimination               true
% 2.71/0.99  --inst_learning_loop_flag               true
% 2.71/0.99  --inst_learning_start                   3000
% 2.71/0.99  --inst_learning_factor                  2
% 2.71/0.99  --inst_start_prop_sim_after_learn       3
% 2.71/0.99  --inst_sel_renew                        solver
% 2.71/0.99  --inst_lit_activity_flag                true
% 2.71/0.99  --inst_restr_to_given                   false
% 2.71/0.99  --inst_activity_threshold               500
% 2.71/0.99  --inst_out_proof                        true
% 2.71/0.99  
% 2.71/0.99  ------ Resolution Options
% 2.71/0.99  
% 2.71/0.99  --resolution_flag                       true
% 2.71/0.99  --res_lit_sel                           adaptive
% 2.71/0.99  --res_lit_sel_side                      none
% 2.71/0.99  --res_ordering                          kbo
% 2.71/0.99  --res_to_prop_solver                    active
% 2.71/0.99  --res_prop_simpl_new                    false
% 2.71/0.99  --res_prop_simpl_given                  true
% 2.71/0.99  --res_passive_queue_type                priority_queues
% 2.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.99  --res_passive_queues_freq               [15;5]
% 2.71/0.99  --res_forward_subs                      full
% 2.71/0.99  --res_backward_subs                     full
% 2.71/0.99  --res_forward_subs_resolution           true
% 2.71/0.99  --res_backward_subs_resolution          true
% 2.71/0.99  --res_orphan_elimination                true
% 2.71/0.99  --res_time_limit                        2.
% 2.71/0.99  --res_out_proof                         true
% 2.71/0.99  
% 2.71/0.99  ------ Superposition Options
% 2.71/0.99  
% 2.71/0.99  --superposition_flag                    true
% 2.71/0.99  --sup_passive_queue_type                priority_queues
% 2.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.99  --demod_completeness_check              fast
% 2.71/0.99  --demod_use_ground                      true
% 2.71/0.99  --sup_to_prop_solver                    passive
% 2.71/0.99  --sup_prop_simpl_new                    true
% 2.71/0.99  --sup_prop_simpl_given                  true
% 2.71/0.99  --sup_fun_splitting                     false
% 2.71/0.99  --sup_smt_interval                      50000
% 2.71/0.99  
% 2.71/0.99  ------ Superposition Simplification Setup
% 2.71/0.99  
% 2.71/0.99  --sup_indices_passive                   []
% 2.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_full_bw                           [BwDemod]
% 2.71/0.99  --sup_immed_triv                        [TrivRules]
% 2.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_immed_bw_main                     []
% 2.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.99  
% 2.71/0.99  ------ Combination Options
% 2.71/0.99  
% 2.71/0.99  --comb_res_mult                         3
% 2.71/0.99  --comb_sup_mult                         2
% 2.71/0.99  --comb_inst_mult                        10
% 2.71/0.99  
% 2.71/0.99  ------ Debug Options
% 2.71/0.99  
% 2.71/0.99  --dbg_backtrace                         false
% 2.71/0.99  --dbg_dump_prop_clauses                 false
% 2.71/0.99  --dbg_dump_prop_clauses_file            -
% 2.71/0.99  --dbg_out_stat                          false
% 2.71/0.99  ------ Parsing...
% 2.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/0.99  ------ Proving...
% 2.71/0.99  ------ Problem Properties 
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  clauses                                 35
% 2.71/0.99  conjectures                             3
% 2.71/0.99  EPR                                     3
% 2.71/0.99  Horn                                    30
% 2.71/0.99  unary                                   10
% 2.71/0.99  binary                                  8
% 2.71/0.99  lits                                    93
% 2.71/0.99  lits eq                                 40
% 2.71/0.99  fd_pure                                 0
% 2.71/0.99  fd_pseudo                               0
% 2.71/0.99  fd_cond                                 3
% 2.71/0.99  fd_pseudo_cond                          0
% 2.71/0.99  AC symbols                              0
% 2.71/0.99  
% 2.71/0.99  ------ Schedule dynamic 5 is on 
% 2.71/0.99  
% 2.71/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  ------ 
% 2.71/0.99  Current options:
% 2.71/0.99  ------ 
% 2.71/0.99  
% 2.71/0.99  ------ Input Options
% 2.71/0.99  
% 2.71/0.99  --out_options                           all
% 2.71/0.99  --tptp_safe_out                         true
% 2.71/0.99  --problem_path                          ""
% 2.71/0.99  --include_path                          ""
% 2.71/0.99  --clausifier                            res/vclausify_rel
% 2.71/0.99  --clausifier_options                    --mode clausify
% 2.71/0.99  --stdin                                 false
% 2.71/0.99  --stats_out                             all
% 2.71/0.99  
% 2.71/0.99  ------ General Options
% 2.71/0.99  
% 2.71/0.99  --fof                                   false
% 2.71/0.99  --time_out_real                         305.
% 2.71/0.99  --time_out_virtual                      -1.
% 2.71/0.99  --symbol_type_check                     false
% 2.71/0.99  --clausify_out                          false
% 2.71/0.99  --sig_cnt_out                           false
% 2.71/0.99  --trig_cnt_out                          false
% 2.71/0.99  --trig_cnt_out_tolerance                1.
% 2.71/0.99  --trig_cnt_out_sk_spl                   false
% 2.71/0.99  --abstr_cl_out                          false
% 2.71/0.99  
% 2.71/0.99  ------ Global Options
% 2.71/0.99  
% 2.71/0.99  --schedule                              default
% 2.71/0.99  --add_important_lit                     false
% 2.71/0.99  --prop_solver_per_cl                    1000
% 2.71/0.99  --min_unsat_core                        false
% 2.71/0.99  --soft_assumptions                      false
% 2.71/0.99  --soft_lemma_size                       3
% 2.71/0.99  --prop_impl_unit_size                   0
% 2.71/0.99  --prop_impl_unit                        []
% 2.71/0.99  --share_sel_clauses                     true
% 2.71/0.99  --reset_solvers                         false
% 2.71/0.99  --bc_imp_inh                            [conj_cone]
% 2.71/0.99  --conj_cone_tolerance                   3.
% 2.71/0.99  --extra_neg_conj                        none
% 2.71/0.99  --large_theory_mode                     true
% 2.71/0.99  --prolific_symb_bound                   200
% 2.71/0.99  --lt_threshold                          2000
% 2.71/0.99  --clause_weak_htbl                      true
% 2.71/0.99  --gc_record_bc_elim                     false
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing Options
% 2.71/0.99  
% 2.71/0.99  --preprocessing_flag                    true
% 2.71/0.99  --time_out_prep_mult                    0.1
% 2.71/0.99  --splitting_mode                        input
% 2.71/0.99  --splitting_grd                         true
% 2.71/0.99  --splitting_cvd                         false
% 2.71/0.99  --splitting_cvd_svl                     false
% 2.71/0.99  --splitting_nvd                         32
% 2.71/0.99  --sub_typing                            true
% 2.71/0.99  --prep_gs_sim                           true
% 2.71/0.99  --prep_unflatten                        true
% 2.71/0.99  --prep_res_sim                          true
% 2.71/0.99  --prep_upred                            true
% 2.71/0.99  --prep_sem_filter                       exhaustive
% 2.71/0.99  --prep_sem_filter_out                   false
% 2.71/0.99  --pred_elim                             true
% 2.71/0.99  --res_sim_input                         true
% 2.71/0.99  --eq_ax_congr_red                       true
% 2.71/0.99  --pure_diseq_elim                       true
% 2.71/0.99  --brand_transform                       false
% 2.71/0.99  --non_eq_to_eq                          false
% 2.71/0.99  --prep_def_merge                        true
% 2.71/0.99  --prep_def_merge_prop_impl              false
% 2.71/0.99  --prep_def_merge_mbd                    true
% 2.71/0.99  --prep_def_merge_tr_red                 false
% 2.71/0.99  --prep_def_merge_tr_cl                  false
% 2.71/0.99  --smt_preprocessing                     true
% 2.71/0.99  --smt_ac_axioms                         fast
% 2.71/0.99  --preprocessed_out                      false
% 2.71/0.99  --preprocessed_stats                    false
% 2.71/0.99  
% 2.71/0.99  ------ Abstraction refinement Options
% 2.71/0.99  
% 2.71/0.99  --abstr_ref                             []
% 2.71/0.99  --abstr_ref_prep                        false
% 2.71/0.99  --abstr_ref_until_sat                   false
% 2.71/0.99  --abstr_ref_sig_restrict                funpre
% 2.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.99  --abstr_ref_under                       []
% 2.71/0.99  
% 2.71/0.99  ------ SAT Options
% 2.71/0.99  
% 2.71/0.99  --sat_mode                              false
% 2.71/0.99  --sat_fm_restart_options                ""
% 2.71/0.99  --sat_gr_def                            false
% 2.71/0.99  --sat_epr_types                         true
% 2.71/0.99  --sat_non_cyclic_types                  false
% 2.71/0.99  --sat_finite_models                     false
% 2.71/0.99  --sat_fm_lemmas                         false
% 2.71/0.99  --sat_fm_prep                           false
% 2.71/0.99  --sat_fm_uc_incr                        true
% 2.71/0.99  --sat_out_model                         small
% 2.71/0.99  --sat_out_clauses                       false
% 2.71/0.99  
% 2.71/0.99  ------ QBF Options
% 2.71/0.99  
% 2.71/0.99  --qbf_mode                              false
% 2.71/0.99  --qbf_elim_univ                         false
% 2.71/0.99  --qbf_dom_inst                          none
% 2.71/0.99  --qbf_dom_pre_inst                      false
% 2.71/0.99  --qbf_sk_in                             false
% 2.71/0.99  --qbf_pred_elim                         true
% 2.71/0.99  --qbf_split                             512
% 2.71/0.99  
% 2.71/0.99  ------ BMC1 Options
% 2.71/0.99  
% 2.71/0.99  --bmc1_incremental                      false
% 2.71/0.99  --bmc1_axioms                           reachable_all
% 2.71/0.99  --bmc1_min_bound                        0
% 2.71/0.99  --bmc1_max_bound                        -1
% 2.71/0.99  --bmc1_max_bound_default                -1
% 2.71/0.99  --bmc1_symbol_reachability              true
% 2.71/0.99  --bmc1_property_lemmas                  false
% 2.71/0.99  --bmc1_k_induction                      false
% 2.71/0.99  --bmc1_non_equiv_states                 false
% 2.71/0.99  --bmc1_deadlock                         false
% 2.71/0.99  --bmc1_ucm                              false
% 2.71/0.99  --bmc1_add_unsat_core                   none
% 2.71/0.99  --bmc1_unsat_core_children              false
% 2.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.99  --bmc1_out_stat                         full
% 2.71/0.99  --bmc1_ground_init                      false
% 2.71/0.99  --bmc1_pre_inst_next_state              false
% 2.71/0.99  --bmc1_pre_inst_state                   false
% 2.71/0.99  --bmc1_pre_inst_reach_state             false
% 2.71/0.99  --bmc1_out_unsat_core                   false
% 2.71/0.99  --bmc1_aig_witness_out                  false
% 2.71/0.99  --bmc1_verbose                          false
% 2.71/0.99  --bmc1_dump_clauses_tptp                false
% 2.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.99  --bmc1_dump_file                        -
% 2.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.99  --bmc1_ucm_extend_mode                  1
% 2.71/0.99  --bmc1_ucm_init_mode                    2
% 2.71/0.99  --bmc1_ucm_cone_mode                    none
% 2.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.99  --bmc1_ucm_relax_model                  4
% 2.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.99  --bmc1_ucm_layered_model                none
% 2.71/0.99  --bmc1_ucm_max_lemma_size               10
% 2.71/0.99  
% 2.71/0.99  ------ AIG Options
% 2.71/0.99  
% 2.71/0.99  --aig_mode                              false
% 2.71/0.99  
% 2.71/0.99  ------ Instantiation Options
% 2.71/0.99  
% 2.71/0.99  --instantiation_flag                    true
% 2.71/0.99  --inst_sos_flag                         false
% 2.71/0.99  --inst_sos_phase                        true
% 2.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.99  --inst_lit_sel_side                     none
% 2.71/0.99  --inst_solver_per_active                1400
% 2.71/0.99  --inst_solver_calls_frac                1.
% 2.71/0.99  --inst_passive_queue_type               priority_queues
% 2.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.99  --inst_passive_queues_freq              [25;2]
% 2.71/0.99  --inst_dismatching                      true
% 2.71/0.99  --inst_eager_unprocessed_to_passive     true
% 2.71/0.99  --inst_prop_sim_given                   true
% 2.71/0.99  --inst_prop_sim_new                     false
% 2.71/0.99  --inst_subs_new                         false
% 2.71/0.99  --inst_eq_res_simp                      false
% 2.71/0.99  --inst_subs_given                       false
% 2.71/0.99  --inst_orphan_elimination               true
% 2.71/0.99  --inst_learning_loop_flag               true
% 2.71/0.99  --inst_learning_start                   3000
% 2.71/0.99  --inst_learning_factor                  2
% 2.71/0.99  --inst_start_prop_sim_after_learn       3
% 2.71/0.99  --inst_sel_renew                        solver
% 2.71/0.99  --inst_lit_activity_flag                true
% 2.71/0.99  --inst_restr_to_given                   false
% 2.71/0.99  --inst_activity_threshold               500
% 2.71/0.99  --inst_out_proof                        true
% 2.71/0.99  
% 2.71/0.99  ------ Resolution Options
% 2.71/0.99  
% 2.71/0.99  --resolution_flag                       false
% 2.71/0.99  --res_lit_sel                           adaptive
% 2.71/0.99  --res_lit_sel_side                      none
% 2.71/0.99  --res_ordering                          kbo
% 2.71/0.99  --res_to_prop_solver                    active
% 2.71/0.99  --res_prop_simpl_new                    false
% 2.71/0.99  --res_prop_simpl_given                  true
% 2.71/0.99  --res_passive_queue_type                priority_queues
% 2.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.99  --res_passive_queues_freq               [15;5]
% 2.71/0.99  --res_forward_subs                      full
% 2.71/0.99  --res_backward_subs                     full
% 2.71/0.99  --res_forward_subs_resolution           true
% 2.71/0.99  --res_backward_subs_resolution          true
% 2.71/0.99  --res_orphan_elimination                true
% 2.71/0.99  --res_time_limit                        2.
% 2.71/0.99  --res_out_proof                         true
% 2.71/0.99  
% 2.71/0.99  ------ Superposition Options
% 2.71/0.99  
% 2.71/0.99  --superposition_flag                    true
% 2.71/0.99  --sup_passive_queue_type                priority_queues
% 2.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.99  --demod_completeness_check              fast
% 2.71/0.99  --demod_use_ground                      true
% 2.71/0.99  --sup_to_prop_solver                    passive
% 2.71/0.99  --sup_prop_simpl_new                    true
% 2.71/0.99  --sup_prop_simpl_given                  true
% 2.71/0.99  --sup_fun_splitting                     false
% 2.71/0.99  --sup_smt_interval                      50000
% 2.71/0.99  
% 2.71/0.99  ------ Superposition Simplification Setup
% 2.71/0.99  
% 2.71/0.99  --sup_indices_passive                   []
% 2.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_full_bw                           [BwDemod]
% 2.71/0.99  --sup_immed_triv                        [TrivRules]
% 2.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_immed_bw_main                     []
% 2.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.99  
% 2.71/0.99  ------ Combination Options
% 2.71/0.99  
% 2.71/0.99  --comb_res_mult                         3
% 2.71/0.99  --comb_sup_mult                         2
% 2.71/0.99  --comb_inst_mult                        10
% 2.71/0.99  
% 2.71/0.99  ------ Debug Options
% 2.71/0.99  
% 2.71/0.99  --dbg_backtrace                         false
% 2.71/0.99  --dbg_dump_prop_clauses                 false
% 2.71/0.99  --dbg_dump_prop_clauses_file            -
% 2.71/0.99  --dbg_out_stat                          false
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  ------ Proving...
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  % SZS status Theorem for theBenchmark.p
% 2.71/0.99  
% 2.71/0.99   Resolution empty clause
% 2.71/0.99  
% 2.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/0.99  
% 2.71/0.99  fof(f16,axiom,(
% 2.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f36,plain,(
% 2.71/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(ennf_transformation,[],[f16])).
% 2.71/0.99  
% 2.71/0.99  fof(f37,plain,(
% 2.71/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(flattening,[],[f36])).
% 2.71/0.99  
% 2.71/0.99  fof(f46,plain,(
% 2.71/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(nnf_transformation,[],[f37])).
% 2.71/0.99  
% 2.71/0.99  fof(f70,plain,(
% 2.71/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.99    inference(cnf_transformation,[],[f46])).
% 2.71/0.99  
% 2.71/0.99  fof(f18,conjecture,(
% 2.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f19,negated_conjecture,(
% 2.71/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.71/0.99    inference(negated_conjecture,[],[f18])).
% 2.71/0.99  
% 2.71/0.99  fof(f40,plain,(
% 2.71/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.71/0.99    inference(ennf_transformation,[],[f19])).
% 2.71/0.99  
% 2.71/0.99  fof(f41,plain,(
% 2.71/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.71/0.99    inference(flattening,[],[f40])).
% 2.71/0.99  
% 2.71/0.99  fof(f47,plain,(
% 2.71/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.71/0.99    introduced(choice_axiom,[])).
% 2.71/0.99  
% 2.71/0.99  fof(f48,plain,(
% 2.71/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f47])).
% 2.71/0.99  
% 2.71/0.99  fof(f80,plain,(
% 2.71/0.99    v1_funct_2(sK3,sK1,sK2)),
% 2.71/0.99    inference(cnf_transformation,[],[f48])).
% 2.71/0.99  
% 2.71/0.99  fof(f81,plain,(
% 2.71/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.71/0.99    inference(cnf_transformation,[],[f48])).
% 2.71/0.99  
% 2.71/0.99  fof(f12,axiom,(
% 2.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f31,plain,(
% 2.71/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(ennf_transformation,[],[f12])).
% 2.71/0.99  
% 2.71/0.99  fof(f65,plain,(
% 2.71/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.99    inference(cnf_transformation,[],[f31])).
% 2.71/0.99  
% 2.71/0.99  fof(f10,axiom,(
% 2.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f28,plain,(
% 2.71/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.99    inference(ennf_transformation,[],[f10])).
% 2.71/0.99  
% 2.71/0.99  fof(f29,plain,(
% 2.71/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.99    inference(flattening,[],[f28])).
% 2.71/0.99  
% 2.71/0.99  fof(f63,plain,(
% 2.71/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.99    inference(cnf_transformation,[],[f29])).
% 2.71/0.99  
% 2.71/0.99  fof(f82,plain,(
% 2.71/0.99    v2_funct_1(sK3)),
% 2.71/0.99    inference(cnf_transformation,[],[f48])).
% 2.71/0.99  
% 2.71/0.99  fof(f79,plain,(
% 2.71/0.99    v1_funct_1(sK3)),
% 2.71/0.99    inference(cnf_transformation,[],[f48])).
% 2.71/0.99  
% 2.71/0.99  fof(f11,axiom,(
% 2.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f30,plain,(
% 2.71/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(ennf_transformation,[],[f11])).
% 2.71/0.99  
% 2.71/0.99  fof(f64,plain,(
% 2.71/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.99    inference(cnf_transformation,[],[f30])).
% 2.71/0.99  
% 2.71/0.99  fof(f17,axiom,(
% 2.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f38,plain,(
% 2.71/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.99    inference(ennf_transformation,[],[f17])).
% 2.71/0.99  
% 2.71/0.99  fof(f39,plain,(
% 2.71/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.99    inference(flattening,[],[f38])).
% 2.71/0.99  
% 2.71/0.99  fof(f78,plain,(
% 2.71/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.99    inference(cnf_transformation,[],[f39])).
% 2.71/0.99  
% 2.71/0.99  fof(f13,axiom,(
% 2.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f32,plain,(
% 2.71/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(ennf_transformation,[],[f13])).
% 2.71/0.99  
% 2.71/0.99  fof(f66,plain,(
% 2.71/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.99    inference(cnf_transformation,[],[f32])).
% 2.71/0.99  
% 2.71/0.99  fof(f83,plain,(
% 2.71/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 2.71/0.99    inference(cnf_transformation,[],[f48])).
% 2.71/0.99  
% 2.71/0.99  fof(f62,plain,(
% 2.71/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.99    inference(cnf_transformation,[],[f29])).
% 2.71/0.99  
% 2.71/0.99  fof(f8,axiom,(
% 2.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f26,plain,(
% 2.71/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/0.99    inference(ennf_transformation,[],[f8])).
% 2.71/0.99  
% 2.71/0.99  fof(f27,plain,(
% 2.71/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/0.99    inference(flattening,[],[f26])).
% 2.71/0.99  
% 2.71/0.99  fof(f58,plain,(
% 2.71/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.99    inference(cnf_transformation,[],[f27])).
% 2.71/0.99  
% 2.71/0.99  fof(f57,plain,(
% 2.71/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.99    inference(cnf_transformation,[],[f27])).
% 2.71/0.99  
% 2.71/0.99  fof(f77,plain,(
% 2.71/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/0.99    inference(cnf_transformation,[],[f39])).
% 2.71/0.99  
% 2.71/0.99  fof(f84,plain,(
% 2.71/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 2.71/0.99    inference(cnf_transformation,[],[f48])).
% 2.71/0.99  
% 2.71/0.99  fof(f3,axiom,(
% 2.71/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f42,plain,(
% 2.71/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.71/0.99    inference(nnf_transformation,[],[f3])).
% 2.71/0.99  
% 2.71/0.99  fof(f43,plain,(
% 2.71/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.71/0.99    inference(flattening,[],[f42])).
% 2.71/0.99  
% 2.71/0.99  fof(f52,plain,(
% 2.71/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.71/0.99    inference(cnf_transformation,[],[f43])).
% 2.71/0.99  
% 2.71/0.99  fof(f86,plain,(
% 2.71/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.71/0.99    inference(equality_resolution,[],[f52])).
% 2.71/0.99  
% 2.71/0.99  fof(f14,axiom,(
% 2.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f33,plain,(
% 2.71/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(ennf_transformation,[],[f14])).
% 2.71/0.99  
% 2.71/0.99  fof(f34,plain,(
% 2.71/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/0.99    inference(flattening,[],[f33])).
% 2.71/0.99  
% 2.71/0.99  fof(f68,plain,(
% 2.71/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/0.99    inference(cnf_transformation,[],[f34])).
% 2.71/0.99  
% 2.71/0.99  fof(f1,axiom,(
% 2.71/0.99    v1_xboole_0(k1_xboole_0)),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f49,plain,(
% 2.71/0.99    v1_xboole_0(k1_xboole_0)),
% 2.71/0.99    inference(cnf_transformation,[],[f1])).
% 2.71/0.99  
% 2.71/0.99  fof(f15,axiom,(
% 2.71/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.71/0.99  
% 2.71/0.99  fof(f35,plain,(
% 2.71/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.71/0.99    inference(ennf_transformation,[],[f15])).
% 2.71/0.99  
% 2.71/0.99  fof(f69,plain,(
% 2.71/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.71/0.99    inference(cnf_transformation,[],[f35])).
% 2.71/0.99  
% 2.71/0.99  cnf(c_26,plain,
% 2.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.99      | k1_xboole_0 = X2 ),
% 2.71/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_34,negated_conjecture,
% 2.71/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.71/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_520,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.71/0.99      | sK1 != X1
% 2.71/0.99      | sK2 != X2
% 2.71/0.99      | sK3 != X0
% 2.71/0.99      | k1_xboole_0 = X2 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_521,plain,
% 2.71/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.71/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.71/0.99      | k1_xboole_0 = sK2 ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_520]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_33,negated_conjecture,
% 2.71/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.71/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_523,plain,
% 2.71/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_521,c_33]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1450,plain,
% 2.71/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_16,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1453,plain,
% 2.71/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2756,plain,
% 2.71/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1450,c_1453]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2808,plain,
% 2.71/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_523,c_2756]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_13,plain,
% 2.71/0.99      ( ~ v2_funct_1(X0)
% 2.71/0.99      | ~ v1_relat_1(X0)
% 2.71/0.99      | ~ v1_funct_1(X0)
% 2.71/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_32,negated_conjecture,
% 2.71/0.99      ( v2_funct_1(sK3) ),
% 2.71/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_429,plain,
% 2.71/0.99      ( ~ v1_relat_1(X0)
% 2.71/0.99      | ~ v1_funct_1(X0)
% 2.71/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.71/0.99      | sK3 != X0 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_430,plain,
% 2.71/0.99      ( ~ v1_relat_1(sK3)
% 2.71/0.99      | ~ v1_funct_1(sK3)
% 2.71/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_35,negated_conjecture,
% 2.71/0.99      ( v1_funct_1(sK3) ),
% 2.71/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_432,plain,
% 2.71/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_430,c_35]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1446,plain,
% 2.71/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 2.71/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_15,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1713,plain,
% 2.71/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.71/0.99      | v1_relat_1(sK3) ),
% 2.71/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1727,plain,
% 2.71/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_1446,c_35,c_33,c_430,c_1713]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_27,plain,
% 2.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.71/0.99      | ~ v1_relat_1(X0)
% 2.71/0.99      | ~ v1_funct_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1451,plain,
% 2.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.71/0.99      | v1_relat_1(X0) != iProver_top
% 2.71/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2589,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 2.71/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1727,c_1451]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_17,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1452,plain,
% 2.71/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2387,plain,
% 2.71/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_1450,c_1452]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_31,negated_conjecture,
% 2.71/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.71/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2399,plain,
% 2.71/0.99      ( k2_relat_1(sK3) = sK2 ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_2387,c_31]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_14,plain,
% 2.71/0.99      ( ~ v2_funct_1(X0)
% 2.71/0.99      | ~ v1_relat_1(X0)
% 2.71/0.99      | ~ v1_funct_1(X0)
% 2.71/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_415,plain,
% 2.71/0.99      ( ~ v1_relat_1(X0)
% 2.71/0.99      | ~ v1_funct_1(X0)
% 2.71/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.71/0.99      | sK3 != X0 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_416,plain,
% 2.71/0.99      ( ~ v1_relat_1(sK3)
% 2.71/0.99      | ~ v1_funct_1(sK3)
% 2.71/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_415]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_418,plain,
% 2.71/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.71/0.99      inference(global_propositional_subsumption,[status(thm)],[c_416,c_35]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1447,plain,
% 2.71/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 2.71/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1731,plain,
% 2.71/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_1447,c_35,c_33,c_416,c_1713]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2506,plain,
% 2.71/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_2399,c_1731]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2601,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 2.71/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_2589,c_2506]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_36,plain,
% 2.71/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_38,plain,
% 2.71/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1714,plain,
% 2.71/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.71/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1713]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_8,plain,
% 2.71/0.99      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.71/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1802,plain,
% 2.71/0.99      ( ~ v1_relat_1(sK3) | v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) ),
% 2.71/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1803,plain,
% 2.71/0.99      ( v1_relat_1(sK3) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.71/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_9,plain,
% 2.71/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1806,plain,
% 2.71/0.99      ( v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) | ~ v1_funct_1(sK3) ),
% 2.71/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1807,plain,
% 2.71/0.99      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 2.71/0.99      | v1_relat_1(sK3) != iProver_top
% 2.71/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1806]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3382,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_2601,c_36,c_38,c_1714,c_1803,c_1807]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3389,plain,
% 2.71/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_3382,c_1453]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3398,plain,
% 2.71/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_3389,c_2506]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3441,plain,
% 2.71/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_2808,c_3398]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_28,plain,
% 2.71/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.71/0.99      | ~ v1_relat_1(X0)
% 2.71/0.99      | ~ v1_funct_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_30,negated_conjecture,
% 2.71/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 2.71/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.71/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 2.71/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_679,plain,
% 2.71/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.71/0.99      | ~ v1_relat_1(X0)
% 2.71/0.99      | ~ v1_funct_1(X0)
% 2.71/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.71/0.99      | k1_relat_1(X0) != sK2
% 2.71/0.99      | k2_relat_1(X0) != sK1
% 2.71/0.99      | k2_funct_1(sK3) != X0 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_680,plain,
% 2.71/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.71/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 2.71/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.71/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.71/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_679]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_692,plain,
% 2.71/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.71/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.71/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.71/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.71/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_680,c_15]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1434,plain,
% 2.71/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.71/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_681,plain,
% 2.71/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.71/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1939,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.71/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_1434,c_36,c_38,c_681,c_1714,c_1803,c_1807]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1940,plain,
% 2.71/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.71/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.71/0.99      inference(renaming,[status(thm)],[c_1939]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1943,plain,
% 2.71/0.99      ( k1_relat_1(sK3) != sK1
% 2.71/0.99      | k2_relat_1(sK3) != sK2
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_1940,c_1727,c_1731]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2505,plain,
% 2.71/0.99      ( k1_relat_1(sK3) != sK1
% 2.71/0.99      | sK2 != sK2
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_2399,c_1943]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2509,plain,
% 2.71/0.99      ( k1_relat_1(sK3) != sK1
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.71/0.99      inference(equality_resolution_simp,[status(thm)],[c_2505]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3162,plain,
% 2.71/0.99      ( sK2 = k1_xboole_0
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_2808,c_2509]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3387,plain,
% 2.71/0.99      ( sK2 = k1_xboole_0
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.71/0.99      inference(superposition,[status(thm)],[c_2808,c_3382]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3561,plain,
% 2.71/0.99      ( sK2 = k1_xboole_0 ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_3441,c_3162,c_3387]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3566,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_3561,c_3382]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3,plain,
% 2.71/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.71/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3640,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_3566,c_3]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_18,plain,
% 2.71/0.99      ( v1_funct_2(X0,X1,X2)
% 2.71/0.99      | ~ v1_partfun1(X0,X1)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | ~ v1_funct_1(X0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_0,plain,
% 2.71/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.71/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_20,plain,
% 2.71/0.99      ( v1_partfun1(X0,X1)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | ~ v1_xboole_0(X1) ),
% 2.71/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_346,plain,
% 2.71/0.99      ( v1_partfun1(X0,X1)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | k1_xboole_0 != X1 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_347,plain,
% 2.71/0.99      ( v1_partfun1(X0,k1_xboole_0)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_346]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_376,plain,
% 2.71/0.99      ( v1_funct_2(X0,X1,X2)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.71/0.99      | ~ v1_funct_1(X0)
% 2.71/0.99      | X3 != X0
% 2.71/0.99      | k1_xboole_0 != X1 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_347]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_377,plain,
% 2.71/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.71/0.99      | ~ v1_funct_1(X0) ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_376]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_626,plain,
% 2.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.71/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.71/0.99      | ~ v1_funct_1(X0)
% 2.71/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.71/0.99      | k2_funct_1(sK3) != X0
% 2.71/0.99      | sK1 != X1
% 2.71/0.99      | sK2 != k1_xboole_0 ),
% 2.71/0.99      inference(resolution_lifted,[status(thm)],[c_377,c_30]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_627,plain,
% 2.71/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.71/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.71/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.71/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.71/0.99      | sK2 != k1_xboole_0 ),
% 2.71/0.99      inference(unflattening,[status(thm)],[c_626]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_960,plain,
% 2.71/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.71/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.71/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.71/0.99      | sP0_iProver_split
% 2.71/0.99      | sK2 != k1_xboole_0 ),
% 2.71/0.99      inference(splitting,
% 2.71/0.99                [splitting(split),new_symbols(definition,[])],
% 2.71/0.99                [c_627]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1437,plain,
% 2.71/0.99      ( sK2 != k1_xboole_0
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.71/0.99      | sP0_iProver_split = iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1622,plain,
% 2.71/0.99      ( sK2 != k1_xboole_0
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.71/0.99      | sP0_iProver_split = iProver_top ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_1437,c_3]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_959,plain,
% 2.71/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.71/0.99      | ~ sP0_iProver_split ),
% 2.71/0.99      inference(splitting,
% 2.71/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.71/0.99                [c_627]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1438,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 2.71/0.99      | sP0_iProver_split != iProver_top ),
% 2.71/0.99      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1507,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.71/0.99      | sP0_iProver_split != iProver_top ),
% 2.71/0.99      inference(light_normalisation,[status(thm)],[c_1438,c_3]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_1628,plain,
% 2.71/0.99      ( sK2 != k1_xboole_0
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.71/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.71/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1622,c_1507]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2060,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | sK2 != k1_xboole_0 ),
% 2.71/0.99      inference(global_propositional_subsumption,
% 2.71/0.99                [status(thm)],
% 2.71/0.99                [c_1628,c_36,c_38,c_1714,c_1803]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_2061,plain,
% 2.71/0.99      ( sK2 != k1_xboole_0
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.71/0.99      inference(renaming,[status(thm)],[c_2060]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3574,plain,
% 2.71/0.99      ( k1_xboole_0 != k1_xboole_0
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_3561,c_2061]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3619,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.71/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.71/0.99      inference(equality_resolution_simp,[status(thm)],[c_3574]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3622,plain,
% 2.71/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.71/0.99      inference(demodulation,[status(thm)],[c_3619,c_3]) ).
% 2.71/0.99  
% 2.71/0.99  cnf(c_3642,plain,
% 2.71/0.99      ( $false ),
% 2.71/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_3640,c_3622]) ).
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/0.99  
% 2.71/0.99  ------                               Statistics
% 2.71/0.99  
% 2.71/0.99  ------ General
% 2.71/0.99  
% 2.71/0.99  abstr_ref_over_cycles:                  0
% 2.71/0.99  abstr_ref_under_cycles:                 0
% 2.71/0.99  gc_basic_clause_elim:                   0
% 2.71/0.99  forced_gc_time:                         0
% 2.71/0.99  parsing_time:                           0.009
% 2.71/0.99  unif_index_cands_time:                  0.
% 2.71/0.99  unif_index_add_time:                    0.
% 2.71/0.99  orderings_time:                         0.
% 2.71/0.99  out_proof_time:                         0.008
% 2.71/0.99  total_time:                             0.134
% 2.71/0.99  num_of_symbols:                         52
% 2.71/0.99  num_of_terms:                           2892
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing
% 2.71/0.99  
% 2.71/0.99  num_of_splits:                          1
% 2.71/0.99  num_of_split_atoms:                     1
% 2.71/0.99  num_of_reused_defs:                     0
% 2.71/0.99  num_eq_ax_congr_red:                    5
% 2.71/0.99  num_of_sem_filtered_clauses:            1
% 2.71/0.99  num_of_subtypes:                        0
% 2.71/0.99  monotx_restored_types:                  0
% 2.71/0.99  sat_num_of_epr_types:                   0
% 2.71/0.99  sat_num_of_non_cyclic_types:            0
% 2.71/0.99  sat_guarded_non_collapsed_types:        0
% 2.71/0.99  num_pure_diseq_elim:                    0
% 2.71/0.99  simp_replaced_by:                       0
% 2.71/0.99  res_preprocessed:                       163
% 2.71/0.99  prep_upred:                             0
% 2.71/0.99  prep_unflattend:                        58
% 2.71/0.99  smt_new_axioms:                         0
% 2.71/0.99  pred_elim_cands:                        3
% 2.71/0.99  pred_elim:                              5
% 2.71/0.99  pred_elim_cl:                           0
% 2.71/0.99  pred_elim_cycles:                       7
% 2.71/0.99  merged_defs:                            0
% 2.71/0.99  merged_defs_ncl:                        0
% 2.71/0.99  bin_hyper_res:                          0
% 2.71/0.99  prep_cycles:                            4
% 2.71/0.99  pred_elim_time:                         0.011
% 2.71/0.99  splitting_time:                         0.
% 2.71/0.99  sem_filter_time:                        0.
% 2.71/0.99  monotx_time:                            0.
% 2.71/0.99  subtype_inf_time:                       0.
% 2.71/0.99  
% 2.71/0.99  ------ Problem properties
% 2.71/0.99  
% 2.71/0.99  clauses:                                35
% 2.71/0.99  conjectures:                            3
% 2.71/0.99  epr:                                    3
% 2.71/0.99  horn:                                   30
% 2.71/0.99  ground:                                 18
% 2.71/0.99  unary:                                  10
% 2.71/0.99  binary:                                 8
% 2.71/0.99  lits:                                   93
% 2.71/0.99  lits_eq:                                40
% 2.71/0.99  fd_pure:                                0
% 2.71/0.99  fd_pseudo:                              0
% 2.71/0.99  fd_cond:                                3
% 2.71/0.99  fd_pseudo_cond:                         0
% 2.71/0.99  ac_symbols:                             0
% 2.71/0.99  
% 2.71/0.99  ------ Propositional Solver
% 2.71/0.99  
% 2.71/0.99  prop_solver_calls:                      27
% 2.71/0.99  prop_fast_solver_calls:                 1072
% 2.71/0.99  smt_solver_calls:                       0
% 2.71/0.99  smt_fast_solver_calls:                  0
% 2.71/0.99  prop_num_of_clauses:                    1104
% 2.71/0.99  prop_preprocess_simplified:             5126
% 2.71/0.99  prop_fo_subsumed:                       19
% 2.71/0.99  prop_solver_time:                       0.
% 2.71/0.99  smt_solver_time:                        0.
% 2.71/0.99  smt_fast_solver_time:                   0.
% 2.71/0.99  prop_fast_solver_time:                  0.
% 2.71/0.99  prop_unsat_core_time:                   0.
% 2.71/0.99  
% 2.71/0.99  ------ QBF
% 2.71/0.99  
% 2.71/0.99  qbf_q_res:                              0
% 2.71/0.99  qbf_num_tautologies:                    0
% 2.71/0.99  qbf_prep_cycles:                        0
% 2.71/0.99  
% 2.71/0.99  ------ BMC1
% 2.71/0.99  
% 2.71/0.99  bmc1_current_bound:                     -1
% 2.71/0.99  bmc1_last_solved_bound:                 -1
% 2.71/0.99  bmc1_unsat_core_size:                   -1
% 2.71/0.99  bmc1_unsat_core_parents_size:           -1
% 2.71/0.99  bmc1_merge_next_fun:                    0
% 2.71/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.71/0.99  
% 2.71/0.99  ------ Instantiation
% 2.71/0.99  
% 2.71/0.99  inst_num_of_clauses:                    465
% 2.71/0.99  inst_num_in_passive:                    170
% 2.71/0.99  inst_num_in_active:                     229
% 2.71/0.99  inst_num_in_unprocessed:                66
% 2.71/0.99  inst_num_of_loops:                      270
% 2.71/0.99  inst_num_of_learning_restarts:          0
% 2.71/0.99  inst_num_moves_active_passive:          39
% 2.71/0.99  inst_lit_activity:                      0
% 2.71/0.99  inst_lit_activity_moves:                0
% 2.71/0.99  inst_num_tautologies:                   0
% 2.71/0.99  inst_num_prop_implied:                  0
% 2.71/0.99  inst_num_existing_simplified:           0
% 2.71/0.99  inst_num_eq_res_simplified:             0
% 2.71/0.99  inst_num_child_elim:                    0
% 2.71/0.99  inst_num_of_dismatching_blockings:      83
% 2.71/0.99  inst_num_of_non_proper_insts:           295
% 2.71/0.99  inst_num_of_duplicates:                 0
% 2.71/0.99  inst_inst_num_from_inst_to_res:         0
% 2.71/0.99  inst_dismatching_checking_time:         0.
% 2.71/0.99  
% 2.71/0.99  ------ Resolution
% 2.71/0.99  
% 2.71/0.99  res_num_of_clauses:                     0
% 2.71/0.99  res_num_in_passive:                     0
% 2.71/0.99  res_num_in_active:                      0
% 2.71/0.99  res_num_of_loops:                       167
% 2.71/0.99  res_forward_subset_subsumed:            19
% 2.71/0.99  res_backward_subset_subsumed:           0
% 2.71/0.99  res_forward_subsumed:                   0
% 2.71/0.99  res_backward_subsumed:                  0
% 2.71/0.99  res_forward_subsumption_resolution:     4
% 2.71/0.99  res_backward_subsumption_resolution:    0
% 2.71/0.99  res_clause_to_clause_subsumption:       153
% 2.71/0.99  res_orphan_elimination:                 0
% 2.71/0.99  res_tautology_del:                      34
% 2.71/0.99  res_num_eq_res_simplified:              0
% 2.71/0.99  res_num_sel_changes:                    0
% 2.71/0.99  res_moves_from_active_to_pass:          0
% 2.71/0.99  
% 2.71/0.99  ------ Superposition
% 2.71/0.99  
% 2.71/0.99  sup_time_total:                         0.
% 2.71/0.99  sup_time_generating:                    0.
% 2.71/0.99  sup_time_sim_full:                      0.
% 2.71/0.99  sup_time_sim_immed:                     0.
% 2.71/0.99  
% 2.71/0.99  sup_num_of_clauses:                     49
% 2.71/0.99  sup_num_in_active:                      29
% 2.71/0.99  sup_num_in_passive:                     20
% 2.71/0.99  sup_num_of_loops:                       52
% 2.71/0.99  sup_fw_superposition:                   38
% 2.71/0.99  sup_bw_superposition:                   16
% 2.71/0.99  sup_immediate_simplified:               14
% 2.71/0.99  sup_given_eliminated:                   0
% 2.71/0.99  comparisons_done:                       0
% 2.71/0.99  comparisons_avoided:                    10
% 2.71/0.99  
% 2.71/0.99  ------ Simplifications
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  sim_fw_subset_subsumed:                 6
% 2.71/0.99  sim_bw_subset_subsumed:                 3
% 2.71/0.99  sim_fw_subsumed:                        3
% 2.71/0.99  sim_bw_subsumed:                        3
% 2.71/0.99  sim_fw_subsumption_res:                 3
% 2.71/0.99  sim_bw_subsumption_res:                 1
% 2.71/0.99  sim_tautology_del:                      2
% 2.71/0.99  sim_eq_tautology_del:                   4
% 2.71/0.99  sim_eq_res_simp:                        3
% 2.71/0.99  sim_fw_demodulated:                     14
% 2.71/0.99  sim_bw_demodulated:                     22
% 2.71/0.99  sim_light_normalised:                   12
% 2.71/0.99  sim_joinable_taut:                      0
% 2.71/0.99  sim_joinable_simp:                      0
% 2.71/0.99  sim_ac_normalised:                      0
% 2.71/0.99  sim_smt_subsumption:                    0
% 2.71/0.99  
%------------------------------------------------------------------------------
