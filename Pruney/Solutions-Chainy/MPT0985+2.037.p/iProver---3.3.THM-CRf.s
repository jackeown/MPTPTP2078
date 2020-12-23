%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:27 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  161 (1835 expanded)
%              Number of clauses        :  102 ( 573 expanded)
%              Number of leaves         :   16 ( 363 expanded)
%              Depth                    :   22
%              Number of atoms          :  533 (9976 expanded)
%              Number of equality atoms :  236 (2013 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
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

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f53])).

fof(f92,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f71,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1987,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_25,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_460,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_25,c_23])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_25,c_23])).

cnf(c_465,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_465,c_31])).

cnf(c_1983,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_3296,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1987,c_1983])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_39])).

cnf(c_646,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_1176,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2361,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_2466,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_1175,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2467,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_3482,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3296,c_38,c_646,c_2466,c_2467])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1990,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4139,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1987,c_1990])).

cnf(c_4269,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3482,c_4139])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_500,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_501,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_503,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_40])).

cnf(c_1984,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2320,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2334,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1984,c_40,c_38,c_501,c_2320])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1988,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3876,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_1988])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1989,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3373,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1987,c_1989])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3385,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3373,c_36])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_486,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_487,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_489,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_40])).

cnf(c_1985,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2338,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1985,c_40,c_38,c_487,c_2320])).

cnf(c_3443,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3385,c_2338])).

cnf(c_3906,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3876,c_3443])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2321,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2320])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2400,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2401,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2399,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2403,plain,
    ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2399])).

cnf(c_4633,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3906,c_41,c_43,c_2321,c_2401,c_2403])).

cnf(c_4784,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4269,c_4633])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_762,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2
    | k2_funct_1(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_35])).

cnf(c_763,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_775,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_763,c_18])).

cnf(c_1972,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_2389,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1972,c_2334,c_2338])).

cnf(c_3442,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3385,c_2389])).

cnf(c_3446,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3442])).

cnf(c_3609,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k1_relat_1(sK4) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3446,c_41,c_43,c_2321,c_2389,c_2401,c_3385])).

cnf(c_3610,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3609])).

cnf(c_4788,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4269,c_3610])).

cnf(c_4796,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4784,c_4788])).

cnf(c_5403,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4796,c_4633])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5508,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5403,c_10])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK4) != X0
    | sK2 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_732,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_465,c_30])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_572,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_5])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_739,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_732,c_573])).

cnf(c_1974,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_2209,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1974,c_10])).

cnf(c_116,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK4) != X0
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_465,c_35])).

cnf(c_617,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_618,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_1177,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2323,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1177])).

cnf(c_2324,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2323])).

cnf(c_2326,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2324])).

cnf(c_2631,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2209,c_41,c_43,c_116,c_618,c_2321,c_2326,c_2401])).

cnf(c_5416,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4796,c_2631])).

cnf(c_5474,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5416])).

cnf(c_5476,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5474,c_10])).

cnf(c_5510,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5508,c_5476])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.85/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.99  
% 2.85/0.99  ------  iProver source info
% 2.85/0.99  
% 2.85/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.99  git: non_committed_changes: false
% 2.85/0.99  git: last_make_outside_of_git: false
% 2.85/0.99  
% 2.85/0.99  ------ 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options
% 2.85/0.99  
% 2.85/0.99  --out_options                           all
% 2.85/0.99  --tptp_safe_out                         true
% 2.85/0.99  --problem_path                          ""
% 2.85/0.99  --include_path                          ""
% 2.85/0.99  --clausifier                            res/vclausify_rel
% 2.85/0.99  --clausifier_options                    --mode clausify
% 2.85/0.99  --stdin                                 false
% 2.85/0.99  --stats_out                             all
% 2.85/0.99  
% 2.85/0.99  ------ General Options
% 2.85/0.99  
% 2.85/0.99  --fof                                   false
% 2.85/0.99  --time_out_real                         305.
% 2.85/0.99  --time_out_virtual                      -1.
% 2.85/0.99  --symbol_type_check                     false
% 2.85/0.99  --clausify_out                          false
% 2.85/0.99  --sig_cnt_out                           false
% 2.85/0.99  --trig_cnt_out                          false
% 2.85/0.99  --trig_cnt_out_tolerance                1.
% 2.85/0.99  --trig_cnt_out_sk_spl                   false
% 2.85/0.99  --abstr_cl_out                          false
% 2.85/0.99  
% 2.85/0.99  ------ Global Options
% 2.85/0.99  
% 2.85/0.99  --schedule                              default
% 2.85/0.99  --add_important_lit                     false
% 2.85/0.99  --prop_solver_per_cl                    1000
% 2.85/0.99  --min_unsat_core                        false
% 2.85/0.99  --soft_assumptions                      false
% 2.85/0.99  --soft_lemma_size                       3
% 2.85/0.99  --prop_impl_unit_size                   0
% 2.85/0.99  --prop_impl_unit                        []
% 2.85/0.99  --share_sel_clauses                     true
% 2.85/0.99  --reset_solvers                         false
% 2.85/0.99  --bc_imp_inh                            [conj_cone]
% 2.85/0.99  --conj_cone_tolerance                   3.
% 2.85/0.99  --extra_neg_conj                        none
% 2.85/0.99  --large_theory_mode                     true
% 2.85/0.99  --prolific_symb_bound                   200
% 2.85/0.99  --lt_threshold                          2000
% 2.85/0.99  --clause_weak_htbl                      true
% 2.85/0.99  --gc_record_bc_elim                     false
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing Options
% 2.85/0.99  
% 2.85/0.99  --preprocessing_flag                    true
% 2.85/0.99  --time_out_prep_mult                    0.1
% 2.85/0.99  --splitting_mode                        input
% 2.85/0.99  --splitting_grd                         true
% 2.85/0.99  --splitting_cvd                         false
% 2.85/0.99  --splitting_cvd_svl                     false
% 2.85/0.99  --splitting_nvd                         32
% 2.85/0.99  --sub_typing                            true
% 2.85/0.99  --prep_gs_sim                           true
% 2.85/0.99  --prep_unflatten                        true
% 2.85/0.99  --prep_res_sim                          true
% 2.85/0.99  --prep_upred                            true
% 2.85/0.99  --prep_sem_filter                       exhaustive
% 2.85/0.99  --prep_sem_filter_out                   false
% 2.85/0.99  --pred_elim                             true
% 2.85/0.99  --res_sim_input                         true
% 2.85/0.99  --eq_ax_congr_red                       true
% 2.85/0.99  --pure_diseq_elim                       true
% 2.85/0.99  --brand_transform                       false
% 2.85/0.99  --non_eq_to_eq                          false
% 2.85/0.99  --prep_def_merge                        true
% 2.85/0.99  --prep_def_merge_prop_impl              false
% 2.85/0.99  --prep_def_merge_mbd                    true
% 2.85/0.99  --prep_def_merge_tr_red                 false
% 2.85/0.99  --prep_def_merge_tr_cl                  false
% 2.85/0.99  --smt_preprocessing                     true
% 2.85/0.99  --smt_ac_axioms                         fast
% 2.85/0.99  --preprocessed_out                      false
% 2.85/0.99  --preprocessed_stats                    false
% 2.85/0.99  
% 2.85/0.99  ------ Abstraction refinement Options
% 2.85/0.99  
% 2.85/0.99  --abstr_ref                             []
% 2.85/0.99  --abstr_ref_prep                        false
% 2.85/0.99  --abstr_ref_until_sat                   false
% 2.85/0.99  --abstr_ref_sig_restrict                funpre
% 2.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.99  --abstr_ref_under                       []
% 2.85/0.99  
% 2.85/0.99  ------ SAT Options
% 2.85/0.99  
% 2.85/0.99  --sat_mode                              false
% 2.85/0.99  --sat_fm_restart_options                ""
% 2.85/0.99  --sat_gr_def                            false
% 2.85/0.99  --sat_epr_types                         true
% 2.85/0.99  --sat_non_cyclic_types                  false
% 2.85/0.99  --sat_finite_models                     false
% 2.85/0.99  --sat_fm_lemmas                         false
% 2.85/0.99  --sat_fm_prep                           false
% 2.85/0.99  --sat_fm_uc_incr                        true
% 2.85/0.99  --sat_out_model                         small
% 2.85/0.99  --sat_out_clauses                       false
% 2.85/0.99  
% 2.85/0.99  ------ QBF Options
% 2.85/0.99  
% 2.85/0.99  --qbf_mode                              false
% 2.85/0.99  --qbf_elim_univ                         false
% 2.85/0.99  --qbf_dom_inst                          none
% 2.85/0.99  --qbf_dom_pre_inst                      false
% 2.85/0.99  --qbf_sk_in                             false
% 2.85/0.99  --qbf_pred_elim                         true
% 2.85/0.99  --qbf_split                             512
% 2.85/0.99  
% 2.85/0.99  ------ BMC1 Options
% 2.85/0.99  
% 2.85/0.99  --bmc1_incremental                      false
% 2.85/0.99  --bmc1_axioms                           reachable_all
% 2.85/0.99  --bmc1_min_bound                        0
% 2.85/0.99  --bmc1_max_bound                        -1
% 2.85/0.99  --bmc1_max_bound_default                -1
% 2.85/0.99  --bmc1_symbol_reachability              true
% 2.85/0.99  --bmc1_property_lemmas                  false
% 2.85/0.99  --bmc1_k_induction                      false
% 2.85/0.99  --bmc1_non_equiv_states                 false
% 2.85/0.99  --bmc1_deadlock                         false
% 2.85/0.99  --bmc1_ucm                              false
% 2.85/0.99  --bmc1_add_unsat_core                   none
% 2.85/0.99  --bmc1_unsat_core_children              false
% 2.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.99  --bmc1_out_stat                         full
% 2.85/0.99  --bmc1_ground_init                      false
% 2.85/0.99  --bmc1_pre_inst_next_state              false
% 2.85/0.99  --bmc1_pre_inst_state                   false
% 2.85/0.99  --bmc1_pre_inst_reach_state             false
% 2.85/0.99  --bmc1_out_unsat_core                   false
% 2.85/0.99  --bmc1_aig_witness_out                  false
% 2.85/0.99  --bmc1_verbose                          false
% 2.85/0.99  --bmc1_dump_clauses_tptp                false
% 2.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.99  --bmc1_dump_file                        -
% 2.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.99  --bmc1_ucm_extend_mode                  1
% 2.85/0.99  --bmc1_ucm_init_mode                    2
% 2.85/0.99  --bmc1_ucm_cone_mode                    none
% 2.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.99  --bmc1_ucm_relax_model                  4
% 2.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.99  --bmc1_ucm_layered_model                none
% 2.85/0.99  --bmc1_ucm_max_lemma_size               10
% 2.85/0.99  
% 2.85/0.99  ------ AIG Options
% 2.85/0.99  
% 2.85/0.99  --aig_mode                              false
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation Options
% 2.85/0.99  
% 2.85/0.99  --instantiation_flag                    true
% 2.85/0.99  --inst_sos_flag                         false
% 2.85/0.99  --inst_sos_phase                        true
% 2.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel_side                     num_symb
% 2.85/0.99  --inst_solver_per_active                1400
% 2.85/0.99  --inst_solver_calls_frac                1.
% 2.85/0.99  --inst_passive_queue_type               priority_queues
% 2.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.99  --inst_passive_queues_freq              [25;2]
% 2.85/0.99  --inst_dismatching                      true
% 2.85/0.99  --inst_eager_unprocessed_to_passive     true
% 2.85/0.99  --inst_prop_sim_given                   true
% 2.85/0.99  --inst_prop_sim_new                     false
% 2.85/0.99  --inst_subs_new                         false
% 2.85/0.99  --inst_eq_res_simp                      false
% 2.85/0.99  --inst_subs_given                       false
% 2.85/0.99  --inst_orphan_elimination               true
% 2.85/0.99  --inst_learning_loop_flag               true
% 2.85/0.99  --inst_learning_start                   3000
% 2.85/0.99  --inst_learning_factor                  2
% 2.85/0.99  --inst_start_prop_sim_after_learn       3
% 2.85/0.99  --inst_sel_renew                        solver
% 2.85/0.99  --inst_lit_activity_flag                true
% 2.85/0.99  --inst_restr_to_given                   false
% 2.85/0.99  --inst_activity_threshold               500
% 2.85/0.99  --inst_out_proof                        true
% 2.85/0.99  
% 2.85/0.99  ------ Resolution Options
% 2.85/0.99  
% 2.85/0.99  --resolution_flag                       true
% 2.85/0.99  --res_lit_sel                           adaptive
% 2.85/0.99  --res_lit_sel_side                      none
% 2.85/0.99  --res_ordering                          kbo
% 2.85/0.99  --res_to_prop_solver                    active
% 2.85/0.99  --res_prop_simpl_new                    false
% 2.85/0.99  --res_prop_simpl_given                  true
% 2.85/0.99  --res_passive_queue_type                priority_queues
% 2.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.99  --res_passive_queues_freq               [15;5]
% 2.85/0.99  --res_forward_subs                      full
% 2.85/0.99  --res_backward_subs                     full
% 2.85/0.99  --res_forward_subs_resolution           true
% 2.85/0.99  --res_backward_subs_resolution          true
% 2.85/0.99  --res_orphan_elimination                true
% 2.85/0.99  --res_time_limit                        2.
% 2.85/0.99  --res_out_proof                         true
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Options
% 2.85/0.99  
% 2.85/0.99  --superposition_flag                    true
% 2.85/0.99  --sup_passive_queue_type                priority_queues
% 2.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.99  --demod_completeness_check              fast
% 2.85/0.99  --demod_use_ground                      true
% 2.85/0.99  --sup_to_prop_solver                    passive
% 2.85/0.99  --sup_prop_simpl_new                    true
% 2.85/0.99  --sup_prop_simpl_given                  true
% 2.85/0.99  --sup_fun_splitting                     false
% 2.85/0.99  --sup_smt_interval                      50000
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Simplification Setup
% 2.85/0.99  
% 2.85/0.99  --sup_indices_passive                   []
% 2.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_full_bw                           [BwDemod]
% 2.85/0.99  --sup_immed_triv                        [TrivRules]
% 2.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_immed_bw_main                     []
% 2.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  
% 2.85/0.99  ------ Combination Options
% 2.85/0.99  
% 2.85/0.99  --comb_res_mult                         3
% 2.85/0.99  --comb_sup_mult                         2
% 2.85/0.99  --comb_inst_mult                        10
% 2.85/0.99  
% 2.85/0.99  ------ Debug Options
% 2.85/0.99  
% 2.85/0.99  --dbg_backtrace                         false
% 2.85/0.99  --dbg_dump_prop_clauses                 false
% 2.85/0.99  --dbg_dump_prop_clauses_file            -
% 2.85/0.99  --dbg_out_stat                          false
% 2.85/0.99  ------ Parsing...
% 2.85/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.99  ------ Proving...
% 2.85/0.99  ------ Problem Properties 
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  clauses                                 40
% 2.85/0.99  conjectures                             3
% 2.85/0.99  EPR                                     6
% 2.85/0.99  Horn                                    31
% 2.85/0.99  unary                                   7
% 2.85/0.99  binary                                  12
% 2.85/0.99  lits                                    109
% 2.85/0.99  lits eq                                 38
% 2.85/0.99  fd_pure                                 0
% 2.85/0.99  fd_pseudo                               0
% 2.85/0.99  fd_cond                                 3
% 2.85/0.99  fd_pseudo_cond                          1
% 2.85/0.99  AC symbols                              0
% 2.85/0.99  
% 2.85/0.99  ------ Schedule dynamic 5 is on 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ 
% 2.85/0.99  Current options:
% 2.85/0.99  ------ 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options
% 2.85/0.99  
% 2.85/0.99  --out_options                           all
% 2.85/0.99  --tptp_safe_out                         true
% 2.85/0.99  --problem_path                          ""
% 2.85/0.99  --include_path                          ""
% 2.85/0.99  --clausifier                            res/vclausify_rel
% 2.85/0.99  --clausifier_options                    --mode clausify
% 2.85/0.99  --stdin                                 false
% 2.85/0.99  --stats_out                             all
% 2.85/0.99  
% 2.85/0.99  ------ General Options
% 2.85/0.99  
% 2.85/0.99  --fof                                   false
% 2.85/0.99  --time_out_real                         305.
% 2.85/0.99  --time_out_virtual                      -1.
% 2.85/0.99  --symbol_type_check                     false
% 2.85/0.99  --clausify_out                          false
% 2.85/0.99  --sig_cnt_out                           false
% 2.85/0.99  --trig_cnt_out                          false
% 2.85/0.99  --trig_cnt_out_tolerance                1.
% 2.85/0.99  --trig_cnt_out_sk_spl                   false
% 2.85/0.99  --abstr_cl_out                          false
% 2.85/0.99  
% 2.85/0.99  ------ Global Options
% 2.85/0.99  
% 2.85/0.99  --schedule                              default
% 2.85/0.99  --add_important_lit                     false
% 2.85/0.99  --prop_solver_per_cl                    1000
% 2.85/0.99  --min_unsat_core                        false
% 2.85/0.99  --soft_assumptions                      false
% 2.85/0.99  --soft_lemma_size                       3
% 2.85/0.99  --prop_impl_unit_size                   0
% 2.85/0.99  --prop_impl_unit                        []
% 2.85/0.99  --share_sel_clauses                     true
% 2.85/0.99  --reset_solvers                         false
% 2.85/0.99  --bc_imp_inh                            [conj_cone]
% 2.85/0.99  --conj_cone_tolerance                   3.
% 2.85/0.99  --extra_neg_conj                        none
% 2.85/0.99  --large_theory_mode                     true
% 2.85/0.99  --prolific_symb_bound                   200
% 2.85/0.99  --lt_threshold                          2000
% 2.85/0.99  --clause_weak_htbl                      true
% 2.85/0.99  --gc_record_bc_elim                     false
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing Options
% 2.85/0.99  
% 2.85/0.99  --preprocessing_flag                    true
% 2.85/0.99  --time_out_prep_mult                    0.1
% 2.85/0.99  --splitting_mode                        input
% 2.85/0.99  --splitting_grd                         true
% 2.85/0.99  --splitting_cvd                         false
% 2.85/0.99  --splitting_cvd_svl                     false
% 2.85/0.99  --splitting_nvd                         32
% 2.85/0.99  --sub_typing                            true
% 2.85/0.99  --prep_gs_sim                           true
% 2.85/0.99  --prep_unflatten                        true
% 2.85/0.99  --prep_res_sim                          true
% 2.85/0.99  --prep_upred                            true
% 2.85/0.99  --prep_sem_filter                       exhaustive
% 2.85/0.99  --prep_sem_filter_out                   false
% 2.85/0.99  --pred_elim                             true
% 2.85/0.99  --res_sim_input                         true
% 2.85/0.99  --eq_ax_congr_red                       true
% 2.85/0.99  --pure_diseq_elim                       true
% 2.85/0.99  --brand_transform                       false
% 2.85/0.99  --non_eq_to_eq                          false
% 2.85/0.99  --prep_def_merge                        true
% 2.85/0.99  --prep_def_merge_prop_impl              false
% 2.85/0.99  --prep_def_merge_mbd                    true
% 2.85/0.99  --prep_def_merge_tr_red                 false
% 2.85/0.99  --prep_def_merge_tr_cl                  false
% 2.85/0.99  --smt_preprocessing                     true
% 2.85/0.99  --smt_ac_axioms                         fast
% 2.85/0.99  --preprocessed_out                      false
% 2.85/0.99  --preprocessed_stats                    false
% 2.85/0.99  
% 2.85/0.99  ------ Abstraction refinement Options
% 2.85/0.99  
% 2.85/0.99  --abstr_ref                             []
% 2.85/0.99  --abstr_ref_prep                        false
% 2.85/0.99  --abstr_ref_until_sat                   false
% 2.85/0.99  --abstr_ref_sig_restrict                funpre
% 2.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.99  --abstr_ref_under                       []
% 2.85/0.99  
% 2.85/0.99  ------ SAT Options
% 2.85/0.99  
% 2.85/0.99  --sat_mode                              false
% 2.85/0.99  --sat_fm_restart_options                ""
% 2.85/0.99  --sat_gr_def                            false
% 2.85/0.99  --sat_epr_types                         true
% 2.85/0.99  --sat_non_cyclic_types                  false
% 2.85/0.99  --sat_finite_models                     false
% 2.85/0.99  --sat_fm_lemmas                         false
% 2.85/0.99  --sat_fm_prep                           false
% 2.85/0.99  --sat_fm_uc_incr                        true
% 2.85/0.99  --sat_out_model                         small
% 2.85/0.99  --sat_out_clauses                       false
% 2.85/0.99  
% 2.85/0.99  ------ QBF Options
% 2.85/0.99  
% 2.85/0.99  --qbf_mode                              false
% 2.85/0.99  --qbf_elim_univ                         false
% 2.85/0.99  --qbf_dom_inst                          none
% 2.85/0.99  --qbf_dom_pre_inst                      false
% 2.85/0.99  --qbf_sk_in                             false
% 2.85/0.99  --qbf_pred_elim                         true
% 2.85/0.99  --qbf_split                             512
% 2.85/0.99  
% 2.85/0.99  ------ BMC1 Options
% 2.85/0.99  
% 2.85/0.99  --bmc1_incremental                      false
% 2.85/0.99  --bmc1_axioms                           reachable_all
% 2.85/0.99  --bmc1_min_bound                        0
% 2.85/0.99  --bmc1_max_bound                        -1
% 2.85/0.99  --bmc1_max_bound_default                -1
% 2.85/0.99  --bmc1_symbol_reachability              true
% 2.85/0.99  --bmc1_property_lemmas                  false
% 2.85/0.99  --bmc1_k_induction                      false
% 2.85/0.99  --bmc1_non_equiv_states                 false
% 2.85/0.99  --bmc1_deadlock                         false
% 2.85/0.99  --bmc1_ucm                              false
% 2.85/0.99  --bmc1_add_unsat_core                   none
% 2.85/0.99  --bmc1_unsat_core_children              false
% 2.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.99  --bmc1_out_stat                         full
% 2.85/0.99  --bmc1_ground_init                      false
% 2.85/0.99  --bmc1_pre_inst_next_state              false
% 2.85/0.99  --bmc1_pre_inst_state                   false
% 2.85/0.99  --bmc1_pre_inst_reach_state             false
% 2.85/0.99  --bmc1_out_unsat_core                   false
% 2.85/0.99  --bmc1_aig_witness_out                  false
% 2.85/0.99  --bmc1_verbose                          false
% 2.85/0.99  --bmc1_dump_clauses_tptp                false
% 2.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.99  --bmc1_dump_file                        -
% 2.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.99  --bmc1_ucm_extend_mode                  1
% 2.85/0.99  --bmc1_ucm_init_mode                    2
% 2.85/0.99  --bmc1_ucm_cone_mode                    none
% 2.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.99  --bmc1_ucm_relax_model                  4
% 2.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.99  --bmc1_ucm_layered_model                none
% 2.85/0.99  --bmc1_ucm_max_lemma_size               10
% 2.85/0.99  
% 2.85/0.99  ------ AIG Options
% 2.85/0.99  
% 2.85/0.99  --aig_mode                              false
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation Options
% 2.85/0.99  
% 2.85/0.99  --instantiation_flag                    true
% 2.85/0.99  --inst_sos_flag                         false
% 2.85/0.99  --inst_sos_phase                        true
% 2.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel_side                     none
% 2.85/0.99  --inst_solver_per_active                1400
% 2.85/0.99  --inst_solver_calls_frac                1.
% 2.85/0.99  --inst_passive_queue_type               priority_queues
% 2.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.99  --inst_passive_queues_freq              [25;2]
% 2.85/0.99  --inst_dismatching                      true
% 2.85/0.99  --inst_eager_unprocessed_to_passive     true
% 2.85/0.99  --inst_prop_sim_given                   true
% 2.85/0.99  --inst_prop_sim_new                     false
% 2.85/0.99  --inst_subs_new                         false
% 2.85/0.99  --inst_eq_res_simp                      false
% 2.85/0.99  --inst_subs_given                       false
% 2.85/0.99  --inst_orphan_elimination               true
% 2.85/0.99  --inst_learning_loop_flag               true
% 2.85/0.99  --inst_learning_start                   3000
% 2.85/0.99  --inst_learning_factor                  2
% 2.85/0.99  --inst_start_prop_sim_after_learn       3
% 2.85/0.99  --inst_sel_renew                        solver
% 2.85/0.99  --inst_lit_activity_flag                true
% 2.85/0.99  --inst_restr_to_given                   false
% 2.85/0.99  --inst_activity_threshold               500
% 2.85/0.99  --inst_out_proof                        true
% 2.85/0.99  
% 2.85/0.99  ------ Resolution Options
% 2.85/0.99  
% 2.85/0.99  --resolution_flag                       false
% 2.85/0.99  --res_lit_sel                           adaptive
% 2.85/0.99  --res_lit_sel_side                      none
% 2.85/0.99  --res_ordering                          kbo
% 2.85/0.99  --res_to_prop_solver                    active
% 2.85/0.99  --res_prop_simpl_new                    false
% 2.85/0.99  --res_prop_simpl_given                  true
% 2.85/0.99  --res_passive_queue_type                priority_queues
% 2.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.99  --res_passive_queues_freq               [15;5]
% 2.85/0.99  --res_forward_subs                      full
% 2.85/0.99  --res_backward_subs                     full
% 2.85/0.99  --res_forward_subs_resolution           true
% 2.85/0.99  --res_backward_subs_resolution          true
% 2.85/0.99  --res_orphan_elimination                true
% 2.85/0.99  --res_time_limit                        2.
% 2.85/0.99  --res_out_proof                         true
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Options
% 2.85/0.99  
% 2.85/0.99  --superposition_flag                    true
% 2.85/0.99  --sup_passive_queue_type                priority_queues
% 2.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.99  --demod_completeness_check              fast
% 2.85/0.99  --demod_use_ground                      true
% 2.85/0.99  --sup_to_prop_solver                    passive
% 2.85/0.99  --sup_prop_simpl_new                    true
% 2.85/0.99  --sup_prop_simpl_given                  true
% 2.85/0.99  --sup_fun_splitting                     false
% 2.85/0.99  --sup_smt_interval                      50000
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Simplification Setup
% 2.85/0.99  
% 2.85/0.99  --sup_indices_passive                   []
% 2.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_full_bw                           [BwDemod]
% 2.85/0.99  --sup_immed_triv                        [TrivRules]
% 2.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_immed_bw_main                     []
% 2.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  
% 2.85/0.99  ------ Combination Options
% 2.85/0.99  
% 2.85/0.99  --comb_res_mult                         3
% 2.85/0.99  --comb_sup_mult                         2
% 2.85/0.99  --comb_inst_mult                        10
% 2.85/0.99  
% 2.85/0.99  ------ Debug Options
% 2.85/0.99  
% 2.85/0.99  --dbg_backtrace                         false
% 2.85/0.99  --dbg_dump_prop_clauses                 false
% 2.85/0.99  --dbg_dump_prop_clauses_file            -
% 2.85/0.99  --dbg_out_stat                          false
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ Proving...
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  % SZS status Theorem for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99   Resolution empty clause
% 2.85/0.99  
% 2.85/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  fof(f18,conjecture,(
% 2.85/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f19,negated_conjecture,(
% 2.85/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.85/0.99    inference(negated_conjecture,[],[f18])).
% 2.85/0.99  
% 2.85/0.99  fof(f37,plain,(
% 2.85/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.85/0.99    inference(ennf_transformation,[],[f19])).
% 2.85/0.99  
% 2.85/0.99  fof(f38,plain,(
% 2.85/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.85/0.99    inference(flattening,[],[f37])).
% 2.85/0.99  
% 2.85/0.99  fof(f53,plain,(
% 2.85/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f54,plain,(
% 2.85/0.99    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f53])).
% 2.85/0.99  
% 2.85/0.99  fof(f92,plain,(
% 2.85/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.85/0.99    inference(cnf_transformation,[],[f54])).
% 2.85/0.99  
% 2.85/0.99  fof(f15,axiom,(
% 2.85/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f32,plain,(
% 2.85/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.85/0.99    inference(ennf_transformation,[],[f15])).
% 2.85/0.99  
% 2.85/0.99  fof(f80,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f32])).
% 2.85/0.99  
% 2.85/0.99  fof(f14,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f30,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f14])).
% 2.85/0.99  
% 2.85/0.99  fof(f31,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(flattening,[],[f30])).
% 2.85/0.99  
% 2.85/0.99  fof(f79,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f31])).
% 2.85/0.99  
% 2.85/0.99  fof(f16,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f33,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f16])).
% 2.85/0.99  
% 2.85/0.99  fof(f34,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(flattening,[],[f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f52,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(nnf_transformation,[],[f34])).
% 2.85/0.99  
% 2.85/0.99  fof(f81,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f52])).
% 2.85/0.99  
% 2.85/0.99  fof(f91,plain,(
% 2.85/0.99    v1_funct_2(sK4,sK2,sK3)),
% 2.85/0.99    inference(cnf_transformation,[],[f54])).
% 2.85/0.99  
% 2.85/0.99  fof(f12,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f28,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f12])).
% 2.85/0.99  
% 2.85/0.99  fof(f76,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f28])).
% 2.85/0.99  
% 2.85/0.99  fof(f8,axiom,(
% 2.85/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f23,plain,(
% 2.85/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.99    inference(ennf_transformation,[],[f8])).
% 2.85/0.99  
% 2.85/0.99  fof(f24,plain,(
% 2.85/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.99    inference(flattening,[],[f23])).
% 2.85/0.99  
% 2.85/0.99  fof(f72,plain,(
% 2.85/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f24])).
% 2.85/0.99  
% 2.85/0.99  fof(f93,plain,(
% 2.85/0.99    v2_funct_1(sK4)),
% 2.85/0.99    inference(cnf_transformation,[],[f54])).
% 2.85/0.99  
% 2.85/0.99  fof(f90,plain,(
% 2.85/0.99    v1_funct_1(sK4)),
% 2.85/0.99    inference(cnf_transformation,[],[f54])).
% 2.85/0.99  
% 2.85/0.99  fof(f9,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f25,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f9])).
% 2.85/0.99  
% 2.85/0.99  fof(f73,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f25])).
% 2.85/0.99  
% 2.85/0.99  fof(f17,axiom,(
% 2.85/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f35,plain,(
% 2.85/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.99    inference(ennf_transformation,[],[f17])).
% 2.85/0.99  
% 2.85/0.99  fof(f36,plain,(
% 2.85/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.99    inference(flattening,[],[f35])).
% 2.85/0.99  
% 2.85/0.99  fof(f89,plain,(
% 2.85/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f36])).
% 2.85/0.99  
% 2.85/0.99  fof(f13,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f29,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f13])).
% 2.85/0.99  
% 2.85/0.99  fof(f77,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f29])).
% 2.85/0.99  
% 2.85/0.99  fof(f94,plain,(
% 2.85/0.99    k2_relset_1(sK2,sK3,sK4) = sK3),
% 2.85/0.99    inference(cnf_transformation,[],[f54])).
% 2.85/0.99  
% 2.85/0.99  fof(f71,plain,(
% 2.85/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f24])).
% 2.85/0.99  
% 2.85/0.99  fof(f7,axiom,(
% 2.85/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f21,plain,(
% 2.85/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.99    inference(ennf_transformation,[],[f7])).
% 2.85/0.99  
% 2.85/0.99  fof(f22,plain,(
% 2.85/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.99    inference(flattening,[],[f21])).
% 2.85/0.99  
% 2.85/0.99  fof(f70,plain,(
% 2.85/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f22])).
% 2.85/0.99  
% 2.85/0.99  fof(f69,plain,(
% 2.85/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f22])).
% 2.85/0.99  
% 2.85/0.99  fof(f88,plain,(
% 2.85/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f36])).
% 2.85/0.99  
% 2.85/0.99  fof(f95,plain,(
% 2.85/0.99    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 2.85/0.99    inference(cnf_transformation,[],[f54])).
% 2.85/0.99  
% 2.85/0.99  fof(f5,axiom,(
% 2.85/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f49,plain,(
% 2.85/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.85/0.99    inference(nnf_transformation,[],[f5])).
% 2.85/0.99  
% 2.85/0.99  fof(f50,plain,(
% 2.85/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.85/0.99    inference(flattening,[],[f49])).
% 2.85/0.99  
% 2.85/0.99  fof(f65,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.85/0.99    inference(cnf_transformation,[],[f50])).
% 2.85/0.99  
% 2.85/0.99  fof(f99,plain,(
% 2.85/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.85/0.99    inference(equality_resolution,[],[f65])).
% 2.85/0.99  
% 2.85/0.99  fof(f84,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f52])).
% 2.85/0.99  
% 2.85/0.99  fof(f103,plain,(
% 2.85/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.85/0.99    inference(equality_resolution,[],[f84])).
% 2.85/0.99  
% 2.85/0.99  fof(f82,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f52])).
% 2.85/0.99  
% 2.85/0.99  fof(f104,plain,(
% 2.85/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.85/0.99    inference(equality_resolution,[],[f82])).
% 2.85/0.99  
% 2.85/0.99  fof(f3,axiom,(
% 2.85/0.99    v1_xboole_0(k1_xboole_0)),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f60,plain,(
% 2.85/0.99    v1_xboole_0(k1_xboole_0)),
% 2.85/0.99    inference(cnf_transformation,[],[f3])).
% 2.85/0.99  
% 2.85/0.99  cnf(c_38,negated_conjecture,
% 2.85/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.85/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1987,plain,
% 2.85/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_25,plain,
% 2.85/0.99      ( v1_partfun1(X0,X1)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | ~ v1_xboole_0(X1) ),
% 2.85/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_23,plain,
% 2.85/0.99      ( v1_funct_2(X0,X1,X2)
% 2.85/0.99      | ~ v1_partfun1(X0,X1)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | ~ v1_funct_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_460,plain,
% 2.85/0.99      ( v1_funct_2(X0,X1,X2)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.85/0.99      | ~ v1_funct_1(X0)
% 2.85/0.99      | ~ v1_xboole_0(X1) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_25,c_23]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_464,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | v1_funct_2(X0,X1,X2)
% 2.85/0.99      | ~ v1_funct_1(X0)
% 2.85/0.99      | ~ v1_xboole_0(X1) ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_460,c_25,c_23]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_465,plain,
% 2.85/0.99      ( v1_funct_2(X0,X1,X2)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | ~ v1_funct_1(X0)
% 2.85/0.99      | ~ v1_xboole_0(X1) ),
% 2.85/0.99      inference(renaming,[status(thm)],[c_464]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_31,plain,
% 2.85/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.99      | k1_xboole_0 = X2 ),
% 2.85/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_520,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | ~ v1_funct_1(X0)
% 2.85/0.99      | ~ v1_xboole_0(X1)
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.99      | k1_xboole_0 = X2 ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_465,c_31]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1983,plain,
% 2.85/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.85/0.99      | k1_xboole_0 = X1
% 2.85/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.85/0.99      | v1_funct_1(X2) != iProver_top
% 2.85/0.99      | v1_xboole_0(X0) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3296,plain,
% 2.85/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 2.85/0.99      | sK3 = k1_xboole_0
% 2.85/0.99      | v1_funct_1(sK4) != iProver_top
% 2.85/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1987,c_1983]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_39,negated_conjecture,
% 2.85/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.85/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_645,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.99      | sK2 != X1
% 2.85/0.99      | sK3 != X2
% 2.85/0.99      | sK4 != X0
% 2.85/0.99      | k1_xboole_0 = X2 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_39]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_646,plain,
% 2.85/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.85/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.85/0.99      | k1_xboole_0 = sK3 ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_645]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1176,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2361,plain,
% 2.85/0.99      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_1176]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2466,plain,
% 2.85/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_2361]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1175,plain,( X0 = X0 ),theory(equality) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2467,plain,
% 2.85/0.99      ( sK3 = sK3 ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_1175]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3482,plain,
% 2.85/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_3296,c_38,c_646,c_2466,c_2467]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_21,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1990,plain,
% 2.85/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.85/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4139,plain,
% 2.85/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1987,c_1990]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4269,plain,
% 2.85/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_3482,c_4139]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_16,plain,
% 2.85/0.99      ( ~ v2_funct_1(X0)
% 2.85/0.99      | ~ v1_relat_1(X0)
% 2.85/0.99      | ~ v1_funct_1(X0)
% 2.85/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_37,negated_conjecture,
% 2.85/0.99      ( v2_funct_1(sK4) ),
% 2.85/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_500,plain,
% 2.85/0.99      ( ~ v1_relat_1(X0)
% 2.85/0.99      | ~ v1_funct_1(X0)
% 2.85/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.85/0.99      | sK4 != X0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_501,plain,
% 2.85/0.99      ( ~ v1_relat_1(sK4)
% 2.85/0.99      | ~ v1_funct_1(sK4)
% 2.85/0.99      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_500]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_40,negated_conjecture,
% 2.85/0.99      ( v1_funct_1(sK4) ),
% 2.85/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_503,plain,
% 2.85/0.99      ( ~ v1_relat_1(sK4) | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.85/0.99      inference(global_propositional_subsumption,[status(thm)],[c_501,c_40]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1984,plain,
% 2.85/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 2.85/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_18,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2320,plain,
% 2.85/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.85/0.99      | v1_relat_1(sK4) ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2334,plain,
% 2.85/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_1984,c_40,c_38,c_501,c_2320]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_32,plain,
% 2.85/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.85/0.99      | ~ v1_relat_1(X0)
% 2.85/0.99      | ~ v1_funct_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1988,plain,
% 2.85/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.85/0.99      | v1_relat_1(X0) != iProver_top
% 2.85/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3876,plain,
% 2.85/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 2.85/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.85/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_2334,c_1988]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_22,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1989,plain,
% 2.85/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.85/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3373,plain,
% 2.85/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_1987,c_1989]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_36,negated_conjecture,
% 2.85/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 2.85/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3385,plain,
% 2.85/1.00      ( k2_relat_1(sK4) = sK3 ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_3373,c_36]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_17,plain,
% 2.85/1.00      ( ~ v2_funct_1(X0)
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_486,plain,
% 2.85/1.00      ( ~ v1_relat_1(X0)
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.85/1.00      | sK4 != X0 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_487,plain,
% 2.85/1.00      ( ~ v1_relat_1(sK4)
% 2.85/1.00      | ~ v1_funct_1(sK4)
% 2.85/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_489,plain,
% 2.85/1.00      ( ~ v1_relat_1(sK4) | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.85/1.00      inference(global_propositional_subsumption,[status(thm)],[c_487,c_40]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1985,plain,
% 2.85/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 2.85/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2338,plain,
% 2.85/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_1985,c_40,c_38,c_487,c_2320]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3443,plain,
% 2.85/1.00      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_3385,c_2338]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3906,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 2.85/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_3876,c_3443]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_41,plain,
% 2.85/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_43,plain,
% 2.85/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2321,plain,
% 2.85/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.85/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2320]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_14,plain,
% 2.85/1.00      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.85/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2400,plain,
% 2.85/1.00      ( ~ v1_relat_1(sK4) | v1_funct_1(k2_funct_1(sK4)) | ~ v1_funct_1(sK4) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2401,plain,
% 2.85/1.00      ( v1_relat_1(sK4) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 2.85/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_15,plain,
% 2.85/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2399,plain,
% 2.85/1.00      ( v1_relat_1(k2_funct_1(sK4)) | ~ v1_relat_1(sK4) | ~ v1_funct_1(sK4) ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2403,plain,
% 2.85/1.00      ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 2.85/1.00      | v1_relat_1(sK4) != iProver_top
% 2.85/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2399]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4633,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_3906,c_41,c_43,c_2321,c_2401,c_2403]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4784,plain,
% 2.85/1.00      ( sK3 = k1_xboole_0
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_4269,c_4633]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_33,plain,
% 2.85/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | ~ v1_funct_1(X0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_35,negated_conjecture,
% 2.85/1.00      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 2.85/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 2.85/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_762,plain,
% 2.85/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ v1_relat_1(X0)
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | k1_relat_1(X0) != sK3
% 2.85/1.00      | k2_relat_1(X0) != sK2
% 2.85/1.00      | k2_funct_1(sK4) != X0 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_35]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_763,plain,
% 2.85/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.85/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_762]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_775,plain,
% 2.85/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.85/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 2.85/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_763,c_18]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1972,plain,
% 2.85/1.00      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.85/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2389,plain,
% 2.85/1.00      ( k1_relat_1(sK4) != sK2
% 2.85/1.00      | k2_relat_1(sK4) != sK3
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/1.00      inference(light_normalisation,[status(thm)],[c_1972,c_2334,c_2338]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3442,plain,
% 2.85/1.00      ( k1_relat_1(sK4) != sK2
% 2.85/1.00      | sK3 != sK3
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_3385,c_2389]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3446,plain,
% 2.85/1.00      ( k1_relat_1(sK4) != sK2
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/1.00      inference(equality_resolution_simp,[status(thm)],[c_3442]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3609,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | k1_relat_1(sK4) != sK2 ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_3446,c_41,c_43,c_2321,c_2389,c_2401,c_3385]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_3610,plain,
% 2.85/1.00      ( k1_relat_1(sK4) != sK2
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.85/1.00      inference(renaming,[status(thm)],[c_3609]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4788,plain,
% 2.85/1.00      ( sK3 = k1_xboole_0
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.85/1.00      inference(superposition,[status(thm)],[c_4269,c_3610]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_4796,plain,
% 2.85/1.00      ( sK3 = k1_xboole_0 ),
% 2.85/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4784,c_4788]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_5403,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_4796,c_4633]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_10,plain,
% 2.85/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.85/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_5508,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_5403,c_10]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_28,plain,
% 2.85/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.85/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.85/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_731,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.85/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.85/1.00      | k2_funct_1(sK4) != X0
% 2.85/1.00      | sK2 != X1
% 2.85/1.00      | sK3 != k1_xboole_0 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_732,plain,
% 2.85/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 2.85/1.00      | sK3 != k1_xboole_0 ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_731]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_30,plain,
% 2.85/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.85/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.85/1.00      inference(cnf_transformation,[],[f104]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_567,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_xboole_0(X1)
% 2.85/1.00      | X3 != X0
% 2.85/1.00      | X4 != X2
% 2.85/1.00      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 2.85/1.00      | k1_xboole_0 != X1 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_465,c_30]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_568,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.85/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_567]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_5,plain,
% 2.85/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.85/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_572,plain,
% 2.85/1.00      ( ~ v1_funct_1(X0)
% 2.85/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.85/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.85/1.00      inference(global_propositional_subsumption,[status(thm)],[c_568,c_5]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_573,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.85/1.00      inference(renaming,[status(thm)],[c_572]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_739,plain,
% 2.85/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | sK3 != k1_xboole_0 ),
% 2.85/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_732,c_573]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1974,plain,
% 2.85/1.00      ( sK3 != k1_xboole_0
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2209,plain,
% 2.85/1.00      ( sK3 != k1_xboole_0
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_1974,c_10]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_116,plain,
% 2.85/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_616,plain,
% 2.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ v1_funct_1(X0)
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | ~ v1_xboole_0(X1)
% 2.85/1.00      | k2_funct_1(sK4) != X0
% 2.85/1.00      | sK2 != X2
% 2.85/1.00      | sK3 != X1 ),
% 2.85/1.00      inference(resolution_lifted,[status(thm)],[c_465,c_35]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_617,plain,
% 2.85/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.85/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.85/1.00      | ~ v1_xboole_0(sK3) ),
% 2.85/1.00      inference(unflattening,[status(thm)],[c_616]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_618,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.85/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.85/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_1177,plain,
% 2.85/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.85/1.00      theory(equality) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2323,plain,
% 2.85/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_1177]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2324,plain,
% 2.85/1.00      ( sK3 != X0
% 2.85/1.00      | v1_xboole_0(X0) != iProver_top
% 2.85/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.85/1.00      inference(predicate_to_equality,[status(thm)],[c_2323]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2326,plain,
% 2.85/1.00      ( sK3 != k1_xboole_0
% 2.85/1.00      | v1_xboole_0(sK3) = iProver_top
% 2.85/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.85/1.00      inference(instantiation,[status(thm)],[c_2324]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_2631,plain,
% 2.85/1.00      ( sK3 != k1_xboole_0
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.85/1.00      inference(global_propositional_subsumption,
% 2.85/1.00                [status(thm)],
% 2.85/1.00                [c_2209,c_41,c_43,c_116,c_618,c_2321,c_2326,c_2401]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_5416,plain,
% 2.85/1.00      ( k1_xboole_0 != k1_xboole_0
% 2.85/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_4796,c_2631]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_5474,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.85/1.00      inference(equality_resolution_simp,[status(thm)],[c_5416]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_5476,plain,
% 2.85/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.85/1.00      inference(demodulation,[status(thm)],[c_5474,c_10]) ).
% 2.85/1.00  
% 2.85/1.00  cnf(c_5510,plain,
% 2.85/1.00      ( $false ),
% 2.85/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_5508,c_5476]) ).
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/1.00  
% 2.85/1.00  ------                               Statistics
% 2.85/1.00  
% 2.85/1.00  ------ General
% 2.85/1.00  
% 2.85/1.00  abstr_ref_over_cycles:                  0
% 2.85/1.00  abstr_ref_under_cycles:                 0
% 2.85/1.00  gc_basic_clause_elim:                   0
% 2.85/1.00  forced_gc_time:                         0
% 2.85/1.00  parsing_time:                           0.012
% 2.85/1.00  unif_index_cands_time:                  0.
% 2.85/1.00  unif_index_add_time:                    0.
% 2.85/1.00  orderings_time:                         0.
% 2.85/1.00  out_proof_time:                         0.014
% 2.85/1.00  total_time:                             0.176
% 2.85/1.00  num_of_symbols:                         53
% 2.85/1.00  num_of_terms:                           4506
% 2.85/1.00  
% 2.85/1.00  ------ Preprocessing
% 2.85/1.00  
% 2.85/1.00  num_of_splits:                          0
% 2.85/1.00  num_of_split_atoms:                     0
% 2.85/1.00  num_of_reused_defs:                     0
% 2.85/1.00  num_eq_ax_congr_red:                    22
% 2.85/1.00  num_of_sem_filtered_clauses:            1
% 2.85/1.00  num_of_subtypes:                        0
% 2.85/1.00  monotx_restored_types:                  0
% 2.85/1.00  sat_num_of_epr_types:                   0
% 2.85/1.00  sat_num_of_non_cyclic_types:            0
% 2.85/1.00  sat_guarded_non_collapsed_types:        0
% 2.85/1.00  num_pure_diseq_elim:                    0
% 2.85/1.00  simp_replaced_by:                       0
% 2.85/1.00  res_preprocessed:                       187
% 2.85/1.00  prep_upred:                             0
% 2.85/1.00  prep_unflattend:                        52
% 2.85/1.00  smt_new_axioms:                         0
% 2.85/1.00  pred_elim_cands:                        6
% 2.85/1.00  pred_elim:                              3
% 2.85/1.00  pred_elim_cl:                           -2
% 2.85/1.00  pred_elim_cycles:                       5
% 2.85/1.00  merged_defs:                            8
% 2.85/1.00  merged_defs_ncl:                        0
% 2.85/1.00  bin_hyper_res:                          8
% 2.85/1.00  prep_cycles:                            4
% 2.85/1.00  pred_elim_time:                         0.01
% 2.85/1.00  splitting_time:                         0.
% 2.85/1.00  sem_filter_time:                        0.
% 2.85/1.00  monotx_time:                            0.
% 2.85/1.00  subtype_inf_time:                       0.
% 2.85/1.00  
% 2.85/1.00  ------ Problem properties
% 2.85/1.00  
% 2.85/1.00  clauses:                                40
% 2.85/1.00  conjectures:                            3
% 2.85/1.00  epr:                                    6
% 2.85/1.00  horn:                                   31
% 2.85/1.00  ground:                                 15
% 2.85/1.00  unary:                                  7
% 2.85/1.00  binary:                                 12
% 2.85/1.00  lits:                                   109
% 2.85/1.00  lits_eq:                                38
% 2.85/1.00  fd_pure:                                0
% 2.85/1.00  fd_pseudo:                              0
% 2.85/1.00  fd_cond:                                3
% 2.85/1.00  fd_pseudo_cond:                         1
% 2.85/1.00  ac_symbols:                             0
% 2.85/1.00  
% 2.85/1.00  ------ Propositional Solver
% 2.85/1.00  
% 2.85/1.00  prop_solver_calls:                      29
% 2.85/1.00  prop_fast_solver_calls:                 1274
% 2.85/1.00  smt_solver_calls:                       0
% 2.85/1.00  smt_fast_solver_calls:                  0
% 2.85/1.00  prop_num_of_clauses:                    1755
% 2.85/1.00  prop_preprocess_simplified:             6503
% 2.85/1.00  prop_fo_subsumed:                       26
% 2.85/1.00  prop_solver_time:                       0.
% 2.85/1.00  smt_solver_time:                        0.
% 2.85/1.00  smt_fast_solver_time:                   0.
% 2.85/1.00  prop_fast_solver_time:                  0.
% 2.85/1.00  prop_unsat_core_time:                   0.
% 2.85/1.00  
% 2.85/1.00  ------ QBF
% 2.85/1.00  
% 2.85/1.00  qbf_q_res:                              0
% 2.85/1.00  qbf_num_tautologies:                    0
% 2.85/1.00  qbf_prep_cycles:                        0
% 2.85/1.00  
% 2.85/1.00  ------ BMC1
% 2.85/1.00  
% 2.85/1.00  bmc1_current_bound:                     -1
% 2.85/1.00  bmc1_last_solved_bound:                 -1
% 2.85/1.00  bmc1_unsat_core_size:                   -1
% 2.85/1.00  bmc1_unsat_core_parents_size:           -1
% 2.85/1.00  bmc1_merge_next_fun:                    0
% 2.85/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.85/1.00  
% 2.85/1.00  ------ Instantiation
% 2.85/1.00  
% 2.85/1.00  inst_num_of_clauses:                    557
% 2.85/1.00  inst_num_in_passive:                    184
% 2.85/1.00  inst_num_in_active:                     263
% 2.85/1.00  inst_num_in_unprocessed:                110
% 2.85/1.00  inst_num_of_loops:                      360
% 2.85/1.00  inst_num_of_learning_restarts:          0
% 2.85/1.00  inst_num_moves_active_passive:          93
% 2.85/1.00  inst_lit_activity:                      0
% 2.85/1.00  inst_lit_activity_moves:                0
% 2.85/1.00  inst_num_tautologies:                   0
% 2.85/1.00  inst_num_prop_implied:                  0
% 2.85/1.00  inst_num_existing_simplified:           0
% 2.85/1.00  inst_num_eq_res_simplified:             0
% 2.85/1.00  inst_num_child_elim:                    0
% 2.85/1.00  inst_num_of_dismatching_blockings:      172
% 2.85/1.00  inst_num_of_non_proper_insts:           505
% 2.85/1.00  inst_num_of_duplicates:                 0
% 2.85/1.00  inst_inst_num_from_inst_to_res:         0
% 2.85/1.00  inst_dismatching_checking_time:         0.
% 2.85/1.00  
% 2.85/1.00  ------ Resolution
% 2.85/1.00  
% 2.85/1.00  res_num_of_clauses:                     0
% 2.85/1.00  res_num_in_passive:                     0
% 2.85/1.00  res_num_in_active:                      0
% 2.85/1.00  res_num_of_loops:                       191
% 2.85/1.00  res_forward_subset_subsumed:            29
% 2.85/1.00  res_backward_subset_subsumed:           0
% 2.85/1.00  res_forward_subsumed:                   1
% 2.85/1.00  res_backward_subsumed:                  0
% 2.85/1.00  res_forward_subsumption_resolution:     3
% 2.85/1.00  res_backward_subsumption_resolution:    0
% 2.85/1.00  res_clause_to_clause_subsumption:       223
% 2.85/1.00  res_orphan_elimination:                 0
% 2.85/1.00  res_tautology_del:                      56
% 2.85/1.00  res_num_eq_res_simplified:              0
% 2.85/1.00  res_num_sel_changes:                    0
% 2.85/1.00  res_moves_from_active_to_pass:          0
% 2.85/1.00  
% 2.85/1.00  ------ Superposition
% 2.85/1.00  
% 2.85/1.00  sup_time_total:                         0.
% 2.85/1.00  sup_time_generating:                    0.
% 2.85/1.00  sup_time_sim_full:                      0.
% 2.85/1.00  sup_time_sim_immed:                     0.
% 2.85/1.00  
% 2.85/1.00  sup_num_of_clauses:                     66
% 2.85/1.00  sup_num_in_active:                      37
% 2.85/1.00  sup_num_in_passive:                     29
% 2.85/1.00  sup_num_of_loops:                       70
% 2.85/1.00  sup_fw_superposition:                   52
% 2.85/1.00  sup_bw_superposition:                   38
% 2.85/1.00  sup_immediate_simplified:               19
% 2.85/1.00  sup_given_eliminated:                   1
% 2.85/1.00  comparisons_done:                       0
% 2.85/1.00  comparisons_avoided:                    10
% 2.85/1.00  
% 2.85/1.00  ------ Simplifications
% 2.85/1.00  
% 2.85/1.00  
% 2.85/1.00  sim_fw_subset_subsumed:                 15
% 2.85/1.00  sim_bw_subset_subsumed:                 3
% 2.85/1.00  sim_fw_subsumed:                        1
% 2.85/1.00  sim_bw_subsumed:                        4
% 2.85/1.00  sim_fw_subsumption_res:                 3
% 2.85/1.00  sim_bw_subsumption_res:                 1
% 2.85/1.00  sim_tautology_del:                      3
% 2.85/1.00  sim_eq_tautology_del:                   6
% 2.85/1.00  sim_eq_res_simp:                        3
% 2.85/1.00  sim_fw_demodulated:                     18
% 2.85/1.00  sim_bw_demodulated:                     32
% 2.85/1.00  sim_light_normalised:                   9
% 2.85/1.00  sim_joinable_taut:                      0
% 2.85/1.00  sim_joinable_simp:                      0
% 2.85/1.00  sim_ac_normalised:                      0
% 2.85/1.00  sim_smt_subsumption:                    0
% 2.85/1.00  
%------------------------------------------------------------------------------
