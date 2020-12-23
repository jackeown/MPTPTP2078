%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:19 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  240 (7502 expanded)
%              Number of clauses        :  159 (2544 expanded)
%              Number of leaves         :   21 (1420 expanded)
%              Depth                    :   24
%              Number of atoms          :  721 (38447 expanded)
%              Number of equality atoms :  342 (7613 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f52,plain,
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

fof(f53,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f52])).

fof(f89,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f53])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f48])).

fof(f57,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_38])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1366])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1369,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1367,c_37])).

cnf(c_2466,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2469,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4621,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2466,c_2469])).

cnf(c_4998,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1369,c_4621])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3479,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_2471])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_521,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_36])).

cnf(c_522,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_524,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_39])).

cnf(c_2459,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_3603,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3479,c_2459])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2473,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4757,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3603,c_2473])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2794,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2960,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2794])).

cnf(c_2961,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2960])).

cnf(c_5330,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4757,c_40,c_42,c_2961])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | k1_relset_1(X1,X2,X0) = X1
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_1314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_1313])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1318,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1314,c_31])).

cnf(c_2455,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_49,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2853,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2854,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2853])).

cnf(c_4041,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2455,c_49,c_2854])).

cnf(c_5335,plain,
    ( k1_relset_1(k1_relat_1(k4_relat_1(sK3)),k2_relat_1(k4_relat_1(sK3)),k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3))
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5330,c_4041])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_507,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_508,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_510,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_39])).

cnf(c_2460,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_3602,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3479,c_2460])).

cnf(c_3606,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3602,c_3603])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2468,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4146,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2466,c_2468])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4148,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4146,c_35])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_493,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_494,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_496,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_39])).

cnf(c_2461,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_3601,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3479,c_2461])).

cnf(c_3609,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3601,c_3603])).

cnf(c_4255,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4148,c_3609])).

cnf(c_5336,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k4_relat_1(sK3)) = sK2
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5335,c_3606,c_4255])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2472,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4751,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3603,c_2472])).

cnf(c_5365,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k4_relat_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5336,c_40,c_42,c_2961,c_4751])).

cnf(c_5368,plain,
    ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4998,c_5365])).

cnf(c_34,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1473,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k2_relat_1(X0) != sK1
    | k1_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_1474,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1473])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1474,c_18])).

cnf(c_2448,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_1491,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_2774,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2775,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2774])).

cnf(c_3163,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2448,c_40,c_42,c_1491,c_2775,c_2961])).

cnf(c_3164,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3163])).

cnf(c_3614,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | k1_relat_1(k4_relat_1(sK3)) != sK2
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3603,c_3164])).

cnf(c_4493,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_4255])).

cnf(c_4497,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4493,c_3606])).

cnf(c_5221,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4998,c_4497])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1452])).

cnf(c_24,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_418,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_24,c_22])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_9,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_422,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_24,c_22,c_19,c_9])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_29])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1291])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1292,c_0])).

cnf(c_1460,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK2 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1453,c_1296])).

cnf(c_2449,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_134,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_34])).

cnf(c_1338,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1337])).

cnf(c_1339,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1338])).

cnf(c_1823,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2809,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_2810,plain,
    ( sK2 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2809])).

cnf(c_2812,plain,
    ( sK2 != k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_3171,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2449,c_40,c_42,c_134,c_1339,c_2775,c_2812,c_2961])).

cnf(c_3613,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3603,c_3171])).

cnf(c_5306,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5221,c_3613])).

cnf(c_2467,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5381,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3606,c_2467])).

cnf(c_5403,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5381,c_4255])).

cnf(c_5601,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5403,c_40,c_42,c_2961,c_4751,c_4757])).

cnf(c_5606,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4998,c_5601])).

cnf(c_5794,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5368,c_3613,c_5221,c_5606])).

cnf(c_5805,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5794,c_3613])).

cnf(c_5862,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5805])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != X1
    | sK2 != k1_xboole_0
    | sK3 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1431])).

cnf(c_2450,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1432])).

cnf(c_5813,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5794,c_2450])).

cnf(c_5821,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5813])).

cnf(c_5815,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5794,c_2466])).

cnf(c_5825,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5821,c_5815])).

cnf(c_2944,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2945,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2944])).

cnf(c_2947,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2945])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2968,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2969,plain,
    ( sK3 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2968])).

cnf(c_2971,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_5380,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4148,c_2467])).

cnf(c_5531,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5380,c_40,c_42,c_2961])).

cnf(c_5799,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5794,c_5531])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2476,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4256,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4148,c_2476])).

cnf(c_4372,plain,
    ( sK2 != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4256,c_42,c_2961])).

cnf(c_4373,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4372])).

cnf(c_5806,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5794,c_4373])).

cnf(c_5856,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5806])).

cnf(c_5871,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5799,c_5856])).

cnf(c_6389,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5825,c_134,c_2947,c_2971,c_5871])).

cnf(c_2483,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2477,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2482,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3492,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2483,c_2482])).

cnf(c_6121,plain,
    ( k4_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_3492])).

cnf(c_6544,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2483,c_6121])).

cnf(c_7295,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5862,c_6389,c_6544])).

cnf(c_2,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2481,plain,
    ( v1_xboole_0(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6120,plain,
    ( sK0(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2481,c_3492])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2480,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6193,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6120,c_2480])).

cnf(c_7297,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7295,c_6193])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.11/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.99  
% 3.11/0.99  ------  iProver source info
% 3.11/0.99  
% 3.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.99  git: non_committed_changes: false
% 3.11/0.99  git: last_make_outside_of_git: false
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     num_symb
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       true
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  ------ Parsing...
% 3.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.99  ------ Proving...
% 3.11/0.99  ------ Problem Properties 
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  clauses                                 39
% 3.11/0.99  conjectures                             3
% 3.11/0.99  EPR                                     5
% 3.11/0.99  Horn                                    33
% 3.11/0.99  unary                                   6
% 3.11/0.99  binary                                  15
% 3.11/0.99  lits                                    103
% 3.11/0.99  lits eq                                 39
% 3.11/0.99  fd_pure                                 0
% 3.11/0.99  fd_pseudo                               0
% 3.11/0.99  fd_cond                                 2
% 3.11/0.99  fd_pseudo_cond                          1
% 3.11/0.99  AC symbols                              0
% 3.11/0.99  
% 3.11/0.99  ------ Schedule dynamic 5 is on 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  Current options:
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     none
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       false
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ Proving...
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS status Theorem for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99   Resolution empty clause
% 3.11/0.99  
% 3.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  fof(f18,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f42,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f18])).
% 3.11/0.99  
% 3.11/0.99  fof(f43,plain,(
% 3.11/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(flattening,[],[f42])).
% 3.11/0.99  
% 3.11/0.99  fof(f51,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(nnf_transformation,[],[f43])).
% 3.11/0.99  
% 3.11/0.99  fof(f79,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f51])).
% 3.11/0.99  
% 3.11/0.99  fof(f20,conjecture,(
% 3.11/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f21,negated_conjecture,(
% 3.11/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.11/0.99    inference(negated_conjecture,[],[f20])).
% 3.11/0.99  
% 3.11/0.99  fof(f46,plain,(
% 3.11/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.11/0.99    inference(ennf_transformation,[],[f21])).
% 3.11/0.99  
% 3.11/0.99  fof(f47,plain,(
% 3.11/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.11/0.99    inference(flattening,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f52,plain,(
% 3.11/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f53,plain,(
% 3.11/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f52])).
% 3.11/0.99  
% 3.11/0.99  fof(f89,plain,(
% 3.11/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.11/0.99    inference(cnf_transformation,[],[f53])).
% 3.11/0.99  
% 3.11/0.99  fof(f90,plain,(
% 3.11/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.11/0.99    inference(cnf_transformation,[],[f53])).
% 3.11/0.99  
% 3.11/0.99  fof(f14,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f37,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f14])).
% 3.11/0.99  
% 3.11/0.99  fof(f74,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f37])).
% 3.11/0.99  
% 3.11/0.99  fof(f12,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f35,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f12])).
% 3.11/0.99  
% 3.11/0.99  fof(f72,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f9,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f29,plain,(
% 3.11/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f9])).
% 3.11/0.99  
% 3.11/0.99  fof(f30,plain,(
% 3.11/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f29])).
% 3.11/0.99  
% 3.11/0.99  fof(f67,plain,(
% 3.11/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f30])).
% 3.11/0.99  
% 3.11/0.99  fof(f91,plain,(
% 3.11/0.99    v2_funct_1(sK3)),
% 3.11/0.99    inference(cnf_transformation,[],[f53])).
% 3.11/0.99  
% 3.11/0.99  fof(f88,plain,(
% 3.11/0.99    v1_funct_1(sK3)),
% 3.11/0.99    inference(cnf_transformation,[],[f53])).
% 3.11/0.99  
% 3.11/0.99  fof(f10,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f31,plain,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f10])).
% 3.11/0.99  
% 3.11/0.99  fof(f32,plain,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f31])).
% 3.11/0.99  
% 3.11/0.99  fof(f69,plain,(
% 3.11/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f19,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f44,plain,(
% 3.11/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f19])).
% 3.11/0.99  
% 3.11/0.99  fof(f45,plain,(
% 3.11/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f44])).
% 3.11/0.99  
% 3.11/0.99  fof(f86,plain,(
% 3.11/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f45])).
% 3.11/0.99  
% 3.11/0.99  fof(f87,plain,(
% 3.11/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f45])).
% 3.11/0.99  
% 3.11/0.99  fof(f11,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f33,plain,(
% 3.11/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f11])).
% 3.11/0.99  
% 3.11/0.99  fof(f34,plain,(
% 3.11/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f33])).
% 3.11/0.99  
% 3.11/0.99  fof(f71,plain,(
% 3.11/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f15,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f38,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f15])).
% 3.11/0.99  
% 3.11/0.99  fof(f75,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f38])).
% 3.11/0.99  
% 3.11/0.99  fof(f92,plain,(
% 3.11/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.11/0.99    inference(cnf_transformation,[],[f53])).
% 3.11/0.99  
% 3.11/0.99  fof(f70,plain,(
% 3.11/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f68,plain,(
% 3.11/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f93,plain,(
% 3.11/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.11/0.99    inference(cnf_transformation,[],[f53])).
% 3.11/0.99  
% 3.11/0.99  fof(f82,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f51])).
% 3.11/0.99  
% 3.11/0.99  fof(f97,plain,(
% 3.11/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f82])).
% 3.11/0.99  
% 3.11/0.99  fof(f17,axiom,(
% 3.11/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f41,plain,(
% 3.11/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f17])).
% 3.11/0.99  
% 3.11/0.99  fof(f78,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f41])).
% 3.11/0.99  
% 3.11/0.99  fof(f16,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f39,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f16])).
% 3.11/0.99  
% 3.11/0.99  fof(f40,plain,(
% 3.11/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(flattening,[],[f39])).
% 3.11/0.99  
% 3.11/0.99  fof(f77,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f40])).
% 3.11/0.99  
% 3.11/0.99  fof(f13,axiom,(
% 3.11/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f36,plain,(
% 3.11/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f13])).
% 3.11/0.99  
% 3.11/0.99  fof(f73,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f36])).
% 3.11/0.99  
% 3.11/0.99  fof(f7,axiom,(
% 3.11/0.99    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f26,plain,(
% 3.11/0.99    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f7])).
% 3.11/0.99  
% 3.11/0.99  fof(f63,plain,(
% 3.11/0.99    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f26])).
% 3.11/0.99  
% 3.11/0.99  fof(f80,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f51])).
% 3.11/0.99  
% 3.11/0.99  fof(f98,plain,(
% 3.11/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f80])).
% 3.11/0.99  
% 3.11/0.99  fof(f1,axiom,(
% 3.11/0.99    v1_xboole_0(k1_xboole_0)),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f54,plain,(
% 3.11/0.99    v1_xboole_0(k1_xboole_0)),
% 3.11/0.99    inference(cnf_transformation,[],[f1])).
% 3.11/0.99  
% 3.11/0.99  fof(f83,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f51])).
% 3.11/0.99  
% 3.11/0.99  fof(f96,plain,(
% 3.11/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f83])).
% 3.11/0.99  
% 3.11/0.99  fof(f2,axiom,(
% 3.11/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f22,plain,(
% 3.11/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f2])).
% 3.11/0.99  
% 3.11/0.99  fof(f55,plain,(
% 3.11/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f22])).
% 3.11/0.99  
% 3.11/0.99  fof(f6,axiom,(
% 3.11/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f25,plain,(
% 3.11/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f6])).
% 3.11/0.99  
% 3.11/0.99  fof(f50,plain,(
% 3.11/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(nnf_transformation,[],[f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f62,plain,(
% 3.11/0.99    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f50])).
% 3.11/0.99  
% 3.11/0.99  fof(f5,axiom,(
% 3.11/0.99    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f24,plain,(
% 3.11/0.99    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f5])).
% 3.11/0.99  
% 3.11/0.99  fof(f59,plain,(
% 3.11/0.99    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f24])).
% 3.11/0.99  
% 3.11/0.99  fof(f3,axiom,(
% 3.11/0.99    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f48,plain,(
% 3.11/0.99    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f49,plain,(
% 3.11/0.99    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f48])).
% 3.11/0.99  
% 3.11/0.99  fof(f57,plain,(
% 3.11/0.99    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f49])).
% 3.11/0.99  
% 3.11/0.99  fof(f56,plain,(
% 3.11/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f49])).
% 3.11/0.99  
% 3.11/0.99  cnf(c_30,plain,
% 3.11/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.11/0.99      | k1_xboole_0 = X2 ),
% 3.11/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_38,negated_conjecture,
% 3.11/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.11/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1366,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.11/0.99      | sK1 != X1
% 3.11/0.99      | sK2 != X2
% 3.11/0.99      | sK3 != X0
% 3.11/0.99      | k1_xboole_0 = X2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_38]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1367,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.11/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.11/0.99      | k1_xboole_0 = sK2 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_1366]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_37,negated_conjecture,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1369,plain,
% 3.11/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1367,c_37]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2466,plain,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_20,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2469,plain,
% 3.11/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4621,plain,
% 3.11/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2466,c_2469]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4998,plain,
% 3.11/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1369,c_4621]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_18,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2471,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.11/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3479,plain,
% 3.11/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2466,c_2471]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_13,plain,
% 3.11/0.99      ( ~ v2_funct_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_36,negated_conjecture,
% 3.11/0.99      ( v2_funct_1(sK3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_521,plain,
% 3.11/0.99      ( ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.11/0.99      | sK3 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_36]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_522,plain,
% 3.11/0.99      ( ~ v1_funct_1(sK3)
% 3.11/0.99      | ~ v1_relat_1(sK3)
% 3.11/0.99      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_521]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_39,negated_conjecture,
% 3.11/0.99      ( v1_funct_1(sK3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_524,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_522,c_39]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2459,plain,
% 3.11/0.99      ( k2_funct_1(sK3) = k4_relat_1(sK3) | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3603,plain,
% 3.11/0.99      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3479,c_2459]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_14,plain,
% 3.11/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2473,plain,
% 3.11/0.99      ( v1_funct_1(X0) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4757,plain,
% 3.11/0.99      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 3.11/0.99      | v1_funct_1(sK3) != iProver_top
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3603,c_2473]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_40,plain,
% 3.11/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_42,plain,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2794,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2960,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.11/0.99      | v1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2794]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2961,plain,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.11/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2960]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5330,plain,
% 3.11/0.99      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_4757,c_40,c_42,c_2961]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_32,plain,
% 3.11/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1313,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ v1_funct_1(X3)
% 3.11/0.99      | ~ v1_relat_1(X3)
% 3.11/0.99      | X3 != X0
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.11/0.99      | k2_relat_1(X3) != X2
% 3.11/0.99      | k1_relat_1(X3) != X1
% 3.11/0.99      | k1_xboole_0 = X2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1314,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.11/0.99      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_1313]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_31,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1318,plain,
% 3.11/0.99      ( ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.11/0.99      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1314,c_31]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2455,plain,
% 3.11/0.99      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.11/0.99      | k1_xboole_0 = k2_relat_1(X0)
% 3.11/0.99      | v1_funct_1(X0) != iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_49,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.11/0.99      | v1_funct_1(X0) != iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2853,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.11/0.99      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2854,plain,
% 3.11/0.99      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2853]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4041,plain,
% 3.11/0.99      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 3.11/0.99      | v1_funct_1(X0) != iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2455,c_49,c_2854]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5335,plain,
% 3.11/0.99      ( k1_relset_1(k1_relat_1(k4_relat_1(sK3)),k2_relat_1(k4_relat_1(sK3)),k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3))
% 3.11/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_5330,c_4041]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_16,plain,
% 3.11/0.99      ( ~ v2_funct_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_507,plain,
% 3.11/0.99      ( ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.11/0.99      | sK3 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_508,plain,
% 3.11/0.99      ( ~ v1_funct_1(sK3)
% 3.11/0.99      | ~ v1_relat_1(sK3)
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_510,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_508,c_39]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2460,plain,
% 3.11/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3602,plain,
% 3.11/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3479,c_2460]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3606,plain,
% 3.11/0.99      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_3602,c_3603]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_21,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2468,plain,
% 3.11/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4146,plain,
% 3.11/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2466,c_2468]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_35,negated_conjecture,
% 3.11/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.11/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4148,plain,
% 3.11/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_4146,c_35]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_17,plain,
% 3.11/0.99      ( ~ v2_funct_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_493,plain,
% 3.11/0.99      ( ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.11/0.99      | sK3 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_36]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_494,plain,
% 3.11/0.99      ( ~ v1_funct_1(sK3)
% 3.11/0.99      | ~ v1_relat_1(sK3)
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_493]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_496,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_494,c_39]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2461,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3601,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3479,c_2461]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3609,plain,
% 3.11/0.99      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_3601,c_3603]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4255,plain,
% 3.11/0.99      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4148,c_3609]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5336,plain,
% 3.11/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k4_relat_1(sK3)) = sK2
% 3.11/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_5335,c_3606,c_4255]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_15,plain,
% 3.11/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2472,plain,
% 3.11/0.99      ( v1_funct_1(X0) != iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top
% 3.11/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4751,plain,
% 3.11/0.99      ( v1_funct_1(sK3) != iProver_top
% 3.11/0.99      | v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3603,c_2472]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5365,plain,
% 3.11/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k4_relat_1(sK3)) = sK2 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_5336,c_40,c_42,c_2961,c_4751]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5368,plain,
% 3.11/0.99      ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4998,c_5365]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_34,negated_conjecture,
% 3.11/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1473,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k2_funct_1(sK3) != X0
% 3.11/0.99      | k2_relat_1(X0) != sK1
% 3.11/0.99      | k1_relat_1(X0) != sK2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1474,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_1473]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1486,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.11/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1474,c_18]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2448,plain,
% 3.11/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1491,plain,
% 3.11/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2774,plain,
% 3.11/0.99      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2775,plain,
% 3.11/0.99      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.11/0.99      | v1_funct_1(sK3) != iProver_top
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2774]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3163,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2448,c_40,c_42,c_1491,c_2775,c_2961]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3164,plain,
% 3.11/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_3163]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3614,plain,
% 3.11/0.99      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 3.11/0.99      | k1_relat_1(k4_relat_1(sK3)) != sK2
% 3.11/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_3603,c_3164]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4493,plain,
% 3.11/0.99      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 3.11/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3614,c_4255]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4497,plain,
% 3.11/0.99      ( k1_relat_1(sK3) != sK1
% 3.11/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_4493,c_3606]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5221,plain,
% 3.11/0.99      ( sK2 = k1_xboole_0
% 3.11/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4998,c_4497]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_27,plain,
% 3.11/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1452,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.11/0.99      | k2_funct_1(sK3) != X0
% 3.11/0.99      | sK1 != X1
% 3.11/0.99      | sK2 != k1_xboole_0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1453,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.11/0.99      | sK2 != k1_xboole_0 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_1452]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_24,plain,
% 3.11/0.99      ( v1_partfun1(X0,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ v1_xboole_0(X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_22,plain,
% 3.11/0.99      ( v1_funct_2(X0,X1,X2)
% 3.11/0.99      | ~ v1_partfun1(X0,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ v1_funct_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_418,plain,
% 3.11/0.99      ( v1_funct_2(X0,X1,X2)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_xboole_0(X1) ),
% 3.11/0.99      inference(resolution,[status(thm)],[c_24,c_22]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_19,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ v1_xboole_0(X1)
% 3.11/0.99      | v1_xboole_0(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_9,plain,
% 3.11/0.99      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_422,plain,
% 3.11/0.99      ( v1_funct_2(X0,X1,X2)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ v1_xboole_0(X1) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_418,c_24,c_22,c_19,c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_29,plain,
% 3.11/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1291,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 3.11/0.99      | ~ v1_xboole_0(X1)
% 3.11/0.99      | X3 != X0
% 3.11/0.99      | X4 != X2
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 3.11/0.99      | k1_xboole_0 != X1 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_422,c_29]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1292,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_1291]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_0,plain,
% 3.11/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1296,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1292,c_0]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1460,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | sK2 != k1_xboole_0 ),
% 3.11/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1453,c_1296]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2449,plain,
% 3.11/0.99      ( sK2 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_134,plain,
% 3.11/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1337,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | ~ v1_xboole_0(X1)
% 3.11/0.99      | k2_funct_1(sK3) != X0
% 3.11/0.99      | sK1 != X2
% 3.11/0.99      | sK2 != X1 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_422,c_34]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1338,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.11/0.99      | ~ v1_xboole_0(sK2) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_1337]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1339,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.11/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1338]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1823,plain,
% 3.11/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.11/0.99      theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2809,plain,
% 3.11/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1823]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2810,plain,
% 3.11/0.99      ( sK2 != X0
% 3.11/0.99      | v1_xboole_0(X0) != iProver_top
% 3.11/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2809]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2812,plain,
% 3.11/0.99      ( sK2 != k1_xboole_0
% 3.11/0.99      | v1_xboole_0(sK2) = iProver_top
% 3.11/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2810]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3171,plain,
% 3.11/0.99      ( sK2 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2449,c_40,c_42,c_134,c_1339,c_2775,c_2812,c_2961]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3613,plain,
% 3.11/0.99      ( sK2 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_3603,c_3171]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5306,plain,
% 3.11/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5221,c_3613]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2467,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.11/0.99      | v1_funct_1(X0) != iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5381,plain,
% 3.11/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.11/0.99      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.11/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3606,c_2467]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5403,plain,
% 3.11/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.11/0.99      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.11/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_5381,c_4255]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5601,plain,
% 3.11/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_5403,c_40,c_42,c_2961,c_4751,c_4757]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5606,plain,
% 3.11/0.99      ( sK2 = k1_xboole_0
% 3.11/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4998,c_5601]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5794,plain,
% 3.11/0.99      ( sK2 = k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_5368,c_3613,c_5221,c_5606]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5805,plain,
% 3.11/0.99      ( k1_xboole_0 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_5794,c_3613]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5862,plain,
% 3.11/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.11/0.99      inference(equality_resolution_simp,[status(thm)],[c_5805]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_26,plain,
% 3.11/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.11/0.99      | k1_xboole_0 = X1
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1431,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.11/0.99      | sK1 != X1
% 3.11/0.99      | sK2 != k1_xboole_0
% 3.11/0.99      | sK3 != X0
% 3.11/0.99      | k1_xboole_0 = X1
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1432,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.11/0.99      | sK2 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = sK1
% 3.11/0.99      | k1_xboole_0 = sK3 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_1431]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2450,plain,
% 3.11/0.99      ( sK2 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = sK1
% 3.11/0.99      | k1_xboole_0 = sK3
% 3.11/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1432]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5813,plain,
% 3.11/0.99      ( sK1 = k1_xboole_0
% 3.11/0.99      | sK3 = k1_xboole_0
% 3.11/0.99      | k1_xboole_0 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_5794,c_2450]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5821,plain,
% 3.11/0.99      ( sK1 = k1_xboole_0
% 3.11/0.99      | sK3 = k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.11/0.99      inference(equality_resolution_simp,[status(thm)],[c_5813]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5815,plain,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_5794,c_2466]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5825,plain,
% 3.11/1.00      ( sK1 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.11/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5821,c_5815]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2944,plain,
% 3.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/1.00      | ~ v1_xboole_0(X0)
% 3.11/1.00      | v1_xboole_0(sK3) ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2945,plain,
% 3.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.11/1.00      | v1_xboole_0(X0) != iProver_top
% 3.11/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_2944]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2947,plain,
% 3.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.11/1.00      | v1_xboole_0(sK3) = iProver_top
% 3.11/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_2945]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1,plain,
% 3.11/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.11/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2968,plain,
% 3.11/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2969,plain,
% 3.11/1.00      ( sK3 = X0
% 3.11/1.00      | v1_xboole_0(X0) != iProver_top
% 3.11/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_2968]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2971,plain,
% 3.11/1.00      ( sK3 = k1_xboole_0
% 3.11/1.00      | v1_xboole_0(sK3) != iProver_top
% 3.11/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_2969]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5380,plain,
% 3.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top
% 3.11/1.00      | v1_funct_1(sK3) != iProver_top
% 3.11/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_4148,c_2467]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5531,plain,
% 3.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_5380,c_40,c_42,c_2961]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5799,plain,
% 3.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) = iProver_top ),
% 3.11/1.00      inference(demodulation,[status(thm)],[c_5794,c_5531]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7,plain,
% 3.11/1.00      ( ~ v1_relat_1(X0)
% 3.11/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.11/1.00      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.11/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2476,plain,
% 3.11/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.11/1.00      | k1_relat_1(X0) = k1_xboole_0
% 3.11/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_4256,plain,
% 3.11/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.11/1.00      | sK2 != k1_xboole_0
% 3.11/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_4148,c_2476]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_4372,plain,
% 3.11/1.00      ( sK2 != k1_xboole_0 | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_4256,c_42,c_2961]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_4373,plain,
% 3.11/1.00      ( k1_relat_1(sK3) = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.11/1.00      inference(renaming,[status(thm)],[c_4372]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5806,plain,
% 3.11/1.00      ( k1_relat_1(sK3) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.11/1.00      inference(demodulation,[status(thm)],[c_5794,c_4373]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5856,plain,
% 3.11/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.11/1.00      inference(equality_resolution_simp,[status(thm)],[c_5806]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5871,plain,
% 3.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.11/1.00      inference(light_normalisation,[status(thm)],[c_5799,c_5856]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6389,plain,
% 3.11/1.00      ( sK3 = k1_xboole_0 ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_5825,c_134,c_2947,c_2971,c_5871]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2483,plain,
% 3.11/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6,plain,
% 3.11/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2477,plain,
% 3.11/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.11/1.00      | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2482,plain,
% 3.11/1.00      ( X0 = X1
% 3.11/1.00      | v1_xboole_0(X0) != iProver_top
% 3.11/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_3492,plain,
% 3.11/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_2483,c_2482]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6121,plain,
% 3.11/1.00      ( k4_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_2477,c_3492]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6544,plain,
% 3.11/1.00      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_2483,c_6121]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7295,plain,
% 3.11/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.11/1.00      inference(light_normalisation,[status(thm)],[c_5862,c_6389,c_6544]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2,plain,
% 3.11/1.00      ( v1_xboole_0(sK0(X0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2481,plain,
% 3.11/1.00      ( v1_xboole_0(sK0(X0)) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6120,plain,
% 3.11/1.00      ( sK0(X0) = k1_xboole_0 ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_2481,c_3492]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_3,plain,
% 3.11/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2480,plain,
% 3.11/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6193,plain,
% 3.11/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.11/1.00      inference(demodulation,[status(thm)],[c_6120,c_2480]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7297,plain,
% 3.11/1.00      ( $false ),
% 3.11/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7295,c_6193]) ).
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/1.00  
% 3.11/1.00  ------                               Statistics
% 3.11/1.00  
% 3.11/1.00  ------ General
% 3.11/1.00  
% 3.11/1.00  abstr_ref_over_cycles:                  0
% 3.11/1.00  abstr_ref_under_cycles:                 0
% 3.11/1.00  gc_basic_clause_elim:                   0
% 3.11/1.00  forced_gc_time:                         0
% 3.11/1.00  parsing_time:                           0.011
% 3.11/1.00  unif_index_cands_time:                  0.
% 3.11/1.00  unif_index_add_time:                    0.
% 3.11/1.00  orderings_time:                         0.
% 3.11/1.00  out_proof_time:                         0.013
% 3.11/1.00  total_time:                             0.209
% 3.11/1.00  num_of_symbols:                         51
% 3.11/1.00  num_of_terms:                           4203
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing
% 3.11/1.00  
% 3.11/1.00  num_of_splits:                          0
% 3.11/1.00  num_of_split_atoms:                     0
% 3.11/1.00  num_of_reused_defs:                     0
% 3.11/1.00  num_eq_ax_congr_red:                    8
% 3.11/1.00  num_of_sem_filtered_clauses:            1
% 3.11/1.00  num_of_subtypes:                        0
% 3.11/1.00  monotx_restored_types:                  0
% 3.11/1.00  sat_num_of_epr_types:                   0
% 3.11/1.00  sat_num_of_non_cyclic_types:            0
% 3.11/1.00  sat_guarded_non_collapsed_types:        0
% 3.11/1.00  num_pure_diseq_elim:                    0
% 3.11/1.00  simp_replaced_by:                       0
% 3.11/1.00  res_preprocessed:                       182
% 3.11/1.00  prep_upred:                             0
% 3.11/1.00  prep_unflattend:                        85
% 3.11/1.00  smt_new_axioms:                         0
% 3.11/1.00  pred_elim_cands:                        4
% 3.11/1.00  pred_elim:                              3
% 3.11/1.00  pred_elim_cl:                           -3
% 3.11/1.00  pred_elim_cycles:                       6
% 3.11/1.00  merged_defs:                            0
% 3.11/1.00  merged_defs_ncl:                        0
% 3.11/1.00  bin_hyper_res:                          0
% 3.11/1.00  prep_cycles:                            4
% 3.11/1.00  pred_elim_time:                         0.036
% 3.11/1.00  splitting_time:                         0.
% 3.11/1.00  sem_filter_time:                        0.
% 3.11/1.00  monotx_time:                            0.
% 3.11/1.00  subtype_inf_time:                       0.
% 3.11/1.00  
% 3.11/1.00  ------ Problem properties
% 3.11/1.00  
% 3.11/1.00  clauses:                                39
% 3.11/1.00  conjectures:                            3
% 3.11/1.00  epr:                                    5
% 3.11/1.00  horn:                                   33
% 3.11/1.00  ground:                                 15
% 3.11/1.00  unary:                                  6
% 3.11/1.00  binary:                                 15
% 3.11/1.00  lits:                                   103
% 3.11/1.00  lits_eq:                                39
% 3.11/1.00  fd_pure:                                0
% 3.11/1.00  fd_pseudo:                              0
% 3.11/1.00  fd_cond:                                2
% 3.11/1.00  fd_pseudo_cond:                         1
% 3.11/1.00  ac_symbols:                             0
% 3.11/1.00  
% 3.11/1.00  ------ Propositional Solver
% 3.11/1.00  
% 3.11/1.00  prop_solver_calls:                      27
% 3.11/1.00  prop_fast_solver_calls:                 1460
% 3.11/1.00  smt_solver_calls:                       0
% 3.11/1.00  smt_fast_solver_calls:                  0
% 3.11/1.00  prop_num_of_clauses:                    2026
% 3.11/1.00  prop_preprocess_simplified:             7490
% 3.11/1.00  prop_fo_subsumed:                       47
% 3.11/1.00  prop_solver_time:                       0.
% 3.11/1.00  smt_solver_time:                        0.
% 3.11/1.00  smt_fast_solver_time:                   0.
% 3.11/1.00  prop_fast_solver_time:                  0.
% 3.11/1.00  prop_unsat_core_time:                   0.
% 3.11/1.00  
% 3.11/1.00  ------ QBF
% 3.11/1.00  
% 3.11/1.00  qbf_q_res:                              0
% 3.11/1.00  qbf_num_tautologies:                    0
% 3.11/1.00  qbf_prep_cycles:                        0
% 3.11/1.00  
% 3.11/1.00  ------ BMC1
% 3.11/1.00  
% 3.11/1.00  bmc1_current_bound:                     -1
% 3.11/1.00  bmc1_last_solved_bound:                 -1
% 3.11/1.00  bmc1_unsat_core_size:                   -1
% 3.11/1.00  bmc1_unsat_core_parents_size:           -1
% 3.11/1.00  bmc1_merge_next_fun:                    0
% 3.11/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.11/1.00  
% 3.11/1.00  ------ Instantiation
% 3.11/1.00  
% 3.11/1.00  inst_num_of_clauses:                    641
% 3.11/1.00  inst_num_in_passive:                    81
% 3.11/1.00  inst_num_in_active:                     373
% 3.11/1.00  inst_num_in_unprocessed:                187
% 3.11/1.00  inst_num_of_loops:                      470
% 3.11/1.00  inst_num_of_learning_restarts:          0
% 3.11/1.00  inst_num_moves_active_passive:          95
% 3.11/1.00  inst_lit_activity:                      0
% 3.11/1.00  inst_lit_activity_moves:                0
% 3.11/1.00  inst_num_tautologies:                   0
% 3.11/1.00  inst_num_prop_implied:                  0
% 3.11/1.00  inst_num_existing_simplified:           0
% 3.11/1.00  inst_num_eq_res_simplified:             0
% 3.11/1.00  inst_num_child_elim:                    0
% 3.11/1.00  inst_num_of_dismatching_blockings:      239
% 3.11/1.00  inst_num_of_non_proper_insts:           788
% 3.11/1.00  inst_num_of_duplicates:                 0
% 3.11/1.00  inst_inst_num_from_inst_to_res:         0
% 3.11/1.00  inst_dismatching_checking_time:         0.
% 3.11/1.00  
% 3.11/1.00  ------ Resolution
% 3.11/1.00  
% 3.11/1.00  res_num_of_clauses:                     0
% 3.11/1.00  res_num_in_passive:                     0
% 3.11/1.00  res_num_in_active:                      0
% 3.11/1.00  res_num_of_loops:                       186
% 3.11/1.00  res_forward_subset_subsumed:            33
% 3.11/1.00  res_backward_subset_subsumed:           2
% 3.11/1.00  res_forward_subsumed:                   3
% 3.11/1.00  res_backward_subsumed:                  0
% 3.11/1.00  res_forward_subsumption_resolution:     3
% 3.11/1.00  res_backward_subsumption_resolution:    0
% 3.11/1.00  res_clause_to_clause_subsumption:       193
% 3.11/1.00  res_orphan_elimination:                 0
% 3.11/1.00  res_tautology_del:                      107
% 3.11/1.00  res_num_eq_res_simplified:              0
% 3.11/1.00  res_num_sel_changes:                    0
% 3.11/1.00  res_moves_from_active_to_pass:          0
% 3.11/1.00  
% 3.11/1.00  ------ Superposition
% 3.11/1.00  
% 3.11/1.00  sup_time_total:                         0.
% 3.11/1.00  sup_time_generating:                    0.
% 3.11/1.00  sup_time_sim_full:                      0.
% 3.11/1.00  sup_time_sim_immed:                     0.
% 3.11/1.00  
% 3.11/1.00  sup_num_of_clauses:                     69
% 3.11/1.00  sup_num_in_active:                      39
% 3.11/1.00  sup_num_in_passive:                     30
% 3.11/1.00  sup_num_of_loops:                       93
% 3.11/1.00  sup_fw_superposition:                   46
% 3.11/1.00  sup_bw_superposition:                   60
% 3.11/1.00  sup_immediate_simplified:               57
% 3.11/1.00  sup_given_eliminated:                   0
% 3.11/1.00  comparisons_done:                       0
% 3.11/1.00  comparisons_avoided:                    5
% 3.11/1.00  
% 3.11/1.00  ------ Simplifications
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  sim_fw_subset_subsumed:                 21
% 3.11/1.00  sim_bw_subset_subsumed:                 9
% 3.11/1.00  sim_fw_subsumed:                        11
% 3.11/1.00  sim_bw_subsumed:                        3
% 3.11/1.00  sim_fw_subsumption_res:                 2
% 3.11/1.00  sim_bw_subsumption_res:                 0
% 3.11/1.00  sim_tautology_del:                      4
% 3.11/1.00  sim_eq_tautology_del:                   9
% 3.11/1.00  sim_eq_res_simp:                        3
% 3.11/1.00  sim_fw_demodulated:                     8
% 3.11/1.00  sim_bw_demodulated:                     53
% 3.11/1.00  sim_light_normalised:                   36
% 3.11/1.00  sim_joinable_taut:                      0
% 3.11/1.00  sim_joinable_simp:                      0
% 3.11/1.00  sim_ac_normalised:                      0
% 3.11/1.00  sim_smt_subsumption:                    0
% 3.11/1.00  
%------------------------------------------------------------------------------
