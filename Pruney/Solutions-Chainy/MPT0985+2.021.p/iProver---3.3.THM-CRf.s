%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:24 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  225 (10992 expanded)
%              Number of clauses        :  153 (3770 expanded)
%              Number of leaves         :   21 (2072 expanded)
%              Depth                    :   28
%              Number of atoms          :  653 (56997 expanded)
%              Number of equality atoms :  362 (12219 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
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

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f58,plain,
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

fof(f59,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f58])).

fof(f99,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

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
    inference(nnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f98,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK0(X0,X1),X0,X1)
        & v1_funct_1(sK0(X0,X1))
        & v1_relat_1(sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK0(X0,X1),X0,X1)
      & v1_funct_1(sK0(X0,X1))
      & v1_relat_1(sK0(X0,X1))
      & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f56])).

fof(f91,plain,(
    ! [X0,X1] : v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f90,plain,(
    ! [X0,X1] : m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2096,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2112,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5221,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_2112])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_143,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1460,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3263,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_3264,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3263])).

cnf(c_3266,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2101,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3940,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2096,c_2101])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3956,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3940,c_38])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2109,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4035,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3956,c_2109])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2435,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2436,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2435])).

cnf(c_4923,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4035,c_45,c_2436])).

cnf(c_4924,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4923])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_1342,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1341])).

cnf(c_1344,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1342,c_40])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2102,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4756,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2096,c_2102])).

cnf(c_4826,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1344,c_4756])).

cnf(c_2103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3540,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_2103])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_469,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_470,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_472,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_42])).

cnf(c_2092,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_3558,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3540,c_2092])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2097,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3613,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3558,c_2097])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_455,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_456,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_458,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_42])).

cnf(c_2093,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3557,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3540,c_2093])).

cnf(c_3614,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3613,c_3557])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2556,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2557,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2556])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2555,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2559,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2555])).

cnf(c_3785,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_43,c_45,c_2436,c_2557,c_2559])).

cnf(c_4009,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3956,c_3785])).

cnf(c_5092,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_4009])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k2_relat_1(X0) != sK1
    | k1_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_37])).

cnf(c_1366,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1365])).

cnf(c_1378,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1366,c_21])).

cnf(c_2082,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_1367,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(c_2742,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2082,c_43,c_45,c_1367,c_2436,c_2557,c_2559])).

cnf(c_2743,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2742])).

cnf(c_3608,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3557,c_2743])).

cnf(c_3698,plain,
    ( k2_relat_1(sK3) != sK2
    | k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3608,c_3558])).

cnf(c_4010,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3956,c_3698])).

cnf(c_4026,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4010])).

cnf(c_5157,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_4026])).

cnf(c_5318,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5221,c_143,c_3266,c_4924,c_5092,c_5157])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2115,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5324,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5318,c_2115])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_1326,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1325])).

cnf(c_2084,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_1327,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_2723,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK1
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2084,c_43,c_45,c_1327,c_2436,c_2557])).

cnf(c_2724,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2723])).

cnf(c_5353,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(k1_xboole_0)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5324,c_2724])).

cnf(c_32,plain,
    ( v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_58,plain,
    ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_60,plain,
    ( v1_relat_1(sK0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_109,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_111,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_112,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_114,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_13,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_115,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_117,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_132,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_33,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_514,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK0(X2,X3) != X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_515,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0(X1,X2))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_516,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2)
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_518,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1468,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2545,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK0(X1,X2))
    | X0 != sK0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_2546,plain,
    ( X0 != sK0(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2545])).

cnf(c_2548,plain,
    ( k1_xboole_0 != sK0(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(sK0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_3173,plain,
    ( ~ v1_xboole_0(sK0(X0,X1))
    | k1_xboole_0 = sK0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3176,plain,
    ( k1_xboole_0 = sK0(X0,X1)
    | v1_xboole_0(sK0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3173])).

cnf(c_3178,plain,
    ( k1_xboole_0 = sK0(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3176])).

cnf(c_1459,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2661,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_3814,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_3815,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3814])).

cnf(c_1463,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4873,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_4878,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4873])).

cnf(c_1384,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != sK3
    | sK1 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_41])).

cnf(c_2081,plain,
    ( k2_funct_1(sK3) != sK3
    | sK1 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_5355,plain,
    ( k2_funct_1(k1_xboole_0) != k1_xboole_0
    | sK1 != sK2
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5324,c_2081])).

cnf(c_5358,plain,
    ( k1_relset_1(sK1,sK2,k1_xboole_0) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5324,c_1344])).

cnf(c_5569,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5358,c_5092,c_5157])).

cnf(c_4014,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3956,c_3557])).

cnf(c_5345,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5324,c_4014])).

cnf(c_6166,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5345,c_5569])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2108,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6169,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6166,c_2108])).

cnf(c_7255,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(k1_xboole_0)) != sK2
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5353,c_60,c_111,c_114,c_117,c_132,c_143,c_518,c_2548,c_3178,c_3815,c_4878,c_5092,c_5157,c_5355,c_6169])).

cnf(c_5224,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,k1_relat_1(sK3))) != iProver_top
    | v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4009,c_2112])).

cnf(c_2631,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_1(sK3))
    | k2_funct_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_2632,plain,
    ( k2_funct_1(sK3) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2631])).

cnf(c_2634,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | v1_xboole_0(k2_funct_1(sK3)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2632])).

cnf(c_4064,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4014,c_2108])).

cnf(c_4076,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4064])).

cnf(c_6721,plain,
    ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5224,c_42,c_40,c_143,c_2435,c_2555,c_2634,c_4076,c_5092,c_5157])).

cnf(c_6725,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6721,c_5324])).

cnf(c_6729,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6725,c_2115])).

cnf(c_7259,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7255,c_5569,c_6729])).

cnf(c_5359,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5324,c_2096])).

cnf(c_5572,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5569,c_5359])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5580,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5572,c_5])).

cnf(c_4759,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2102])).

cnf(c_5811,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5580,c_4759])).

cnf(c_7260,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7259,c_6,c_5811])).

cnf(c_7263,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7260,c_5580])).

cnf(c_6916,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6729,c_6166])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7263,c_6916])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.62/1.08  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.62/1.08  
% 0.62/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.62/1.08  
% 0.62/1.08  ------  iProver source info
% 0.62/1.08  
% 0.62/1.08  git: date: 2020-06-30 10:37:57 +0100
% 0.62/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.62/1.08  git: non_committed_changes: false
% 0.62/1.08  git: last_make_outside_of_git: false
% 0.62/1.08  
% 0.62/1.08  ------ 
% 0.62/1.08  
% 0.62/1.08  ------ Input Options
% 0.62/1.08  
% 0.62/1.08  --out_options                           all
% 0.62/1.08  --tptp_safe_out                         true
% 0.62/1.08  --problem_path                          ""
% 0.62/1.08  --include_path                          ""
% 0.62/1.08  --clausifier                            res/vclausify_rel
% 0.62/1.08  --clausifier_options                    --mode clausify
% 0.62/1.08  --stdin                                 false
% 0.62/1.08  --stats_out                             all
% 0.62/1.08  
% 0.62/1.08  ------ General Options
% 0.62/1.08  
% 0.62/1.08  --fof                                   false
% 0.62/1.08  --time_out_real                         305.
% 0.62/1.08  --time_out_virtual                      -1.
% 0.62/1.08  --symbol_type_check                     false
% 0.62/1.08  --clausify_out                          false
% 0.62/1.08  --sig_cnt_out                           false
% 0.62/1.08  --trig_cnt_out                          false
% 0.62/1.08  --trig_cnt_out_tolerance                1.
% 0.62/1.08  --trig_cnt_out_sk_spl                   false
% 0.62/1.08  --abstr_cl_out                          false
% 0.62/1.08  
% 0.62/1.08  ------ Global Options
% 0.62/1.08  
% 0.62/1.08  --schedule                              default
% 0.62/1.08  --add_important_lit                     false
% 0.62/1.08  --prop_solver_per_cl                    1000
% 0.62/1.08  --min_unsat_core                        false
% 0.62/1.08  --soft_assumptions                      false
% 0.62/1.08  --soft_lemma_size                       3
% 0.62/1.08  --prop_impl_unit_size                   0
% 0.62/1.08  --prop_impl_unit                        []
% 0.62/1.08  --share_sel_clauses                     true
% 0.62/1.08  --reset_solvers                         false
% 0.62/1.08  --bc_imp_inh                            [conj_cone]
% 0.62/1.08  --conj_cone_tolerance                   3.
% 0.62/1.08  --extra_neg_conj                        none
% 0.62/1.08  --large_theory_mode                     true
% 0.62/1.08  --prolific_symb_bound                   200
% 0.62/1.08  --lt_threshold                          2000
% 0.62/1.08  --clause_weak_htbl                      true
% 0.62/1.08  --gc_record_bc_elim                     false
% 0.62/1.08  
% 0.62/1.08  ------ Preprocessing Options
% 0.62/1.08  
% 0.62/1.08  --preprocessing_flag                    true
% 0.62/1.08  --time_out_prep_mult                    0.1
% 0.62/1.08  --splitting_mode                        input
% 0.62/1.08  --splitting_grd                         true
% 0.62/1.08  --splitting_cvd                         false
% 0.62/1.08  --splitting_cvd_svl                     false
% 0.62/1.08  --splitting_nvd                         32
% 0.62/1.08  --sub_typing                            true
% 0.62/1.08  --prep_gs_sim                           true
% 0.62/1.08  --prep_unflatten                        true
% 0.62/1.08  --prep_res_sim                          true
% 0.62/1.08  --prep_upred                            true
% 0.62/1.08  --prep_sem_filter                       exhaustive
% 0.62/1.08  --prep_sem_filter_out                   false
% 0.62/1.08  --pred_elim                             true
% 0.62/1.08  --res_sim_input                         true
% 0.62/1.08  --eq_ax_congr_red                       true
% 0.62/1.08  --pure_diseq_elim                       true
% 0.62/1.08  --brand_transform                       false
% 0.62/1.08  --non_eq_to_eq                          false
% 0.62/1.08  --prep_def_merge                        true
% 0.62/1.08  --prep_def_merge_prop_impl              false
% 0.62/1.08  --prep_def_merge_mbd                    true
% 0.62/1.08  --prep_def_merge_tr_red                 false
% 0.62/1.08  --prep_def_merge_tr_cl                  false
% 0.62/1.08  --smt_preprocessing                     true
% 0.62/1.08  --smt_ac_axioms                         fast
% 0.62/1.08  --preprocessed_out                      false
% 0.62/1.08  --preprocessed_stats                    false
% 0.62/1.08  
% 0.62/1.08  ------ Abstraction refinement Options
% 0.62/1.08  
% 0.62/1.08  --abstr_ref                             []
% 0.62/1.08  --abstr_ref_prep                        false
% 0.62/1.08  --abstr_ref_until_sat                   false
% 0.62/1.08  --abstr_ref_sig_restrict                funpre
% 0.62/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 0.62/1.08  --abstr_ref_under                       []
% 0.62/1.08  
% 0.62/1.08  ------ SAT Options
% 0.62/1.08  
% 0.62/1.08  --sat_mode                              false
% 0.62/1.08  --sat_fm_restart_options                ""
% 0.62/1.08  --sat_gr_def                            false
% 0.62/1.08  --sat_epr_types                         true
% 0.62/1.08  --sat_non_cyclic_types                  false
% 0.62/1.08  --sat_finite_models                     false
% 0.62/1.08  --sat_fm_lemmas                         false
% 0.62/1.08  --sat_fm_prep                           false
% 0.62/1.08  --sat_fm_uc_incr                        true
% 0.62/1.08  --sat_out_model                         small
% 0.62/1.08  --sat_out_clauses                       false
% 0.62/1.08  
% 0.62/1.08  ------ QBF Options
% 0.62/1.08  
% 0.62/1.08  --qbf_mode                              false
% 0.62/1.08  --qbf_elim_univ                         false
% 0.62/1.08  --qbf_dom_inst                          none
% 0.62/1.08  --qbf_dom_pre_inst                      false
% 0.62/1.08  --qbf_sk_in                             false
% 0.62/1.08  --qbf_pred_elim                         true
% 0.62/1.08  --qbf_split                             512
% 0.62/1.08  
% 0.62/1.08  ------ BMC1 Options
% 0.62/1.08  
% 0.62/1.08  --bmc1_incremental                      false
% 0.62/1.08  --bmc1_axioms                           reachable_all
% 0.62/1.08  --bmc1_min_bound                        0
% 0.62/1.08  --bmc1_max_bound                        -1
% 0.62/1.08  --bmc1_max_bound_default                -1
% 0.62/1.08  --bmc1_symbol_reachability              true
% 0.62/1.08  --bmc1_property_lemmas                  false
% 0.62/1.08  --bmc1_k_induction                      false
% 0.62/1.08  --bmc1_non_equiv_states                 false
% 0.62/1.08  --bmc1_deadlock                         false
% 0.62/1.08  --bmc1_ucm                              false
% 0.62/1.08  --bmc1_add_unsat_core                   none
% 0.62/1.08  --bmc1_unsat_core_children              false
% 0.62/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 0.62/1.08  --bmc1_out_stat                         full
% 0.62/1.08  --bmc1_ground_init                      false
% 0.62/1.08  --bmc1_pre_inst_next_state              false
% 0.62/1.08  --bmc1_pre_inst_state                   false
% 0.62/1.08  --bmc1_pre_inst_reach_state             false
% 0.62/1.08  --bmc1_out_unsat_core                   false
% 0.62/1.08  --bmc1_aig_witness_out                  false
% 0.62/1.08  --bmc1_verbose                          false
% 0.62/1.08  --bmc1_dump_clauses_tptp                false
% 0.62/1.08  --bmc1_dump_unsat_core_tptp             false
% 0.62/1.08  --bmc1_dump_file                        -
% 0.62/1.08  --bmc1_ucm_expand_uc_limit              128
% 0.62/1.08  --bmc1_ucm_n_expand_iterations          6
% 0.62/1.08  --bmc1_ucm_extend_mode                  1
% 0.62/1.08  --bmc1_ucm_init_mode                    2
% 0.62/1.08  --bmc1_ucm_cone_mode                    none
% 0.62/1.08  --bmc1_ucm_reduced_relation_type        0
% 0.62/1.08  --bmc1_ucm_relax_model                  4
% 0.62/1.08  --bmc1_ucm_full_tr_after_sat            true
% 0.62/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 0.62/1.08  --bmc1_ucm_layered_model                none
% 0.62/1.08  --bmc1_ucm_max_lemma_size               10
% 0.62/1.08  
% 0.62/1.08  ------ AIG Options
% 0.62/1.08  
% 0.62/1.08  --aig_mode                              false
% 0.62/1.08  
% 0.62/1.08  ------ Instantiation Options
% 0.62/1.08  
% 0.62/1.08  --instantiation_flag                    true
% 0.62/1.08  --inst_sos_flag                         false
% 0.62/1.08  --inst_sos_phase                        true
% 0.62/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.62/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.62/1.08  --inst_lit_sel_side                     num_symb
% 0.62/1.08  --inst_solver_per_active                1400
% 0.62/1.08  --inst_solver_calls_frac                1.
% 0.62/1.08  --inst_passive_queue_type               priority_queues
% 0.62/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.62/1.08  --inst_passive_queues_freq              [25;2]
% 0.62/1.08  --inst_dismatching                      true
% 0.62/1.08  --inst_eager_unprocessed_to_passive     true
% 0.62/1.08  --inst_prop_sim_given                   true
% 0.62/1.08  --inst_prop_sim_new                     false
% 0.62/1.08  --inst_subs_new                         false
% 0.62/1.08  --inst_eq_res_simp                      false
% 0.62/1.08  --inst_subs_given                       false
% 0.62/1.08  --inst_orphan_elimination               true
% 0.62/1.08  --inst_learning_loop_flag               true
% 0.62/1.08  --inst_learning_start                   3000
% 0.62/1.08  --inst_learning_factor                  2
% 0.62/1.08  --inst_start_prop_sim_after_learn       3
% 0.62/1.08  --inst_sel_renew                        solver
% 0.62/1.08  --inst_lit_activity_flag                true
% 0.62/1.08  --inst_restr_to_given                   false
% 0.62/1.08  --inst_activity_threshold               500
% 0.62/1.08  --inst_out_proof                        true
% 0.62/1.08  
% 0.62/1.08  ------ Resolution Options
% 0.62/1.08  
% 0.62/1.08  --resolution_flag                       true
% 0.62/1.08  --res_lit_sel                           adaptive
% 0.62/1.08  --res_lit_sel_side                      none
% 0.62/1.08  --res_ordering                          kbo
% 0.62/1.08  --res_to_prop_solver                    active
% 0.62/1.08  --res_prop_simpl_new                    false
% 0.62/1.08  --res_prop_simpl_given                  true
% 0.62/1.08  --res_passive_queue_type                priority_queues
% 0.62/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.62/1.08  --res_passive_queues_freq               [15;5]
% 0.62/1.08  --res_forward_subs                      full
% 0.62/1.08  --res_backward_subs                     full
% 0.62/1.08  --res_forward_subs_resolution           true
% 0.62/1.08  --res_backward_subs_resolution          true
% 0.62/1.08  --res_orphan_elimination                true
% 0.62/1.08  --res_time_limit                        2.
% 0.62/1.08  --res_out_proof                         true
% 0.62/1.08  
% 0.62/1.08  ------ Superposition Options
% 0.62/1.08  
% 0.62/1.08  --superposition_flag                    true
% 0.62/1.08  --sup_passive_queue_type                priority_queues
% 0.62/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.62/1.08  --sup_passive_queues_freq               [8;1;4]
% 0.62/1.08  --demod_completeness_check              fast
% 0.62/1.08  --demod_use_ground                      true
% 0.62/1.08  --sup_to_prop_solver                    passive
% 0.62/1.08  --sup_prop_simpl_new                    true
% 0.62/1.08  --sup_prop_simpl_given                  true
% 0.62/1.08  --sup_fun_splitting                     false
% 0.62/1.08  --sup_smt_interval                      50000
% 0.62/1.08  
% 0.62/1.08  ------ Superposition Simplification Setup
% 0.62/1.08  
% 0.62/1.08  --sup_indices_passive                   []
% 0.62/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.62/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.62/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.62/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 0.62/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.62/1.08  --sup_full_bw                           [BwDemod]
% 0.62/1.08  --sup_immed_triv                        [TrivRules]
% 0.62/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.62/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.62/1.08  --sup_immed_bw_main                     []
% 0.62/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.62/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 0.62/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.62/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.62/1.08  
% 0.62/1.08  ------ Combination Options
% 0.62/1.08  
% 0.62/1.08  --comb_res_mult                         3
% 0.62/1.08  --comb_sup_mult                         2
% 0.62/1.08  --comb_inst_mult                        10
% 0.62/1.08  
% 0.62/1.08  ------ Debug Options
% 0.62/1.08  
% 0.62/1.08  --dbg_backtrace                         false
% 0.62/1.08  --dbg_dump_prop_clauses                 false
% 0.62/1.08  --dbg_dump_prop_clauses_file            -
% 0.62/1.08  --dbg_out_stat                          false
% 0.62/1.08  ------ Parsing...
% 0.62/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.62/1.08  
% 0.62/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 0.62/1.08  
% 0.62/1.08  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.62/1.08  
% 0.62/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.62/1.08  ------ Proving...
% 0.62/1.08  ------ Problem Properties 
% 0.62/1.08  
% 0.62/1.08  
% 0.62/1.08  clauses                                 44
% 0.62/1.08  conjectures                             3
% 0.62/1.08  EPR                                     6
% 0.62/1.08  Horn                                    38
% 0.62/1.08  unary                                   11
% 0.62/1.08  binary                                  13
% 0.62/1.08  lits                                    109
% 0.62/1.08  lits eq                                 49
% 0.62/1.08  fd_pure                                 0
% 0.62/1.08  fd_pseudo                               0
% 0.62/1.08  fd_cond                                 5
% 0.62/1.08  fd_pseudo_cond                          1
% 0.62/1.08  AC symbols                              0
% 0.62/1.08  
% 0.62/1.08  ------ Schedule dynamic 5 is on 
% 0.62/1.08  
% 0.62/1.08  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.62/1.08  
% 0.62/1.08  
% 0.62/1.08  ------ 
% 0.62/1.08  Current options:
% 0.62/1.08  ------ 
% 0.62/1.08  
% 0.62/1.08  ------ Input Options
% 0.62/1.08  
% 0.62/1.08  --out_options                           all
% 0.62/1.08  --tptp_safe_out                         true
% 0.62/1.08  --problem_path                          ""
% 0.62/1.08  --include_path                          ""
% 0.62/1.08  --clausifier                            res/vclausify_rel
% 0.62/1.08  --clausifier_options                    --mode clausify
% 0.62/1.08  --stdin                                 false
% 0.62/1.08  --stats_out                             all
% 0.62/1.08  
% 0.62/1.08  ------ General Options
% 0.62/1.08  
% 0.62/1.08  --fof                                   false
% 0.62/1.08  --time_out_real                         305.
% 0.62/1.08  --time_out_virtual                      -1.
% 0.62/1.08  --symbol_type_check                     false
% 0.62/1.08  --clausify_out                          false
% 0.62/1.08  --sig_cnt_out                           false
% 0.62/1.08  --trig_cnt_out                          false
% 0.62/1.08  --trig_cnt_out_tolerance                1.
% 0.62/1.08  --trig_cnt_out_sk_spl                   false
% 0.62/1.08  --abstr_cl_out                          false
% 0.62/1.08  
% 0.62/1.08  ------ Global Options
% 0.62/1.08  
% 0.62/1.08  --schedule                              default
% 0.62/1.08  --add_important_lit                     false
% 0.62/1.08  --prop_solver_per_cl                    1000
% 0.62/1.08  --min_unsat_core                        false
% 0.62/1.08  --soft_assumptions                      false
% 0.62/1.08  --soft_lemma_size                       3
% 0.62/1.08  --prop_impl_unit_size                   0
% 0.62/1.08  --prop_impl_unit                        []
% 0.62/1.08  --share_sel_clauses                     true
% 0.62/1.08  --reset_solvers                         false
% 0.62/1.08  --bc_imp_inh                            [conj_cone]
% 0.62/1.08  --conj_cone_tolerance                   3.
% 0.62/1.08  --extra_neg_conj                        none
% 0.62/1.08  --large_theory_mode                     true
% 0.62/1.08  --prolific_symb_bound                   200
% 0.62/1.08  --lt_threshold                          2000
% 0.62/1.08  --clause_weak_htbl                      true
% 0.62/1.08  --gc_record_bc_elim                     false
% 0.62/1.08  
% 0.62/1.08  ------ Preprocessing Options
% 0.62/1.08  
% 0.62/1.08  --preprocessing_flag                    true
% 0.62/1.08  --time_out_prep_mult                    0.1
% 0.62/1.08  --splitting_mode                        input
% 0.62/1.08  --splitting_grd                         true
% 0.62/1.08  --splitting_cvd                         false
% 0.62/1.08  --splitting_cvd_svl                     false
% 0.62/1.08  --splitting_nvd                         32
% 0.62/1.08  --sub_typing                            true
% 0.62/1.08  --prep_gs_sim                           true
% 0.62/1.08  --prep_unflatten                        true
% 0.62/1.08  --prep_res_sim                          true
% 0.62/1.08  --prep_upred                            true
% 0.62/1.08  --prep_sem_filter                       exhaustive
% 0.62/1.08  --prep_sem_filter_out                   false
% 0.62/1.08  --pred_elim                             true
% 0.62/1.08  --res_sim_input                         true
% 0.62/1.08  --eq_ax_congr_red                       true
% 0.62/1.08  --pure_diseq_elim                       true
% 0.62/1.08  --brand_transform                       false
% 0.62/1.08  --non_eq_to_eq                          false
% 0.62/1.08  --prep_def_merge                        true
% 0.62/1.08  --prep_def_merge_prop_impl              false
% 0.62/1.08  --prep_def_merge_mbd                    true
% 0.62/1.08  --prep_def_merge_tr_red                 false
% 0.62/1.08  --prep_def_merge_tr_cl                  false
% 0.62/1.08  --smt_preprocessing                     true
% 0.62/1.08  --smt_ac_axioms                         fast
% 0.62/1.08  --preprocessed_out                      false
% 0.62/1.08  --preprocessed_stats                    false
% 0.62/1.08  
% 0.62/1.08  ------ Abstraction refinement Options
% 0.62/1.08  
% 0.62/1.08  --abstr_ref                             []
% 0.62/1.08  --abstr_ref_prep                        false
% 0.62/1.08  --abstr_ref_until_sat                   false
% 0.62/1.08  --abstr_ref_sig_restrict                funpre
% 0.62/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 0.62/1.08  --abstr_ref_under                       []
% 0.62/1.08  
% 0.62/1.08  ------ SAT Options
% 0.62/1.08  
% 0.62/1.08  --sat_mode                              false
% 0.62/1.08  --sat_fm_restart_options                ""
% 0.62/1.08  --sat_gr_def                            false
% 0.62/1.08  --sat_epr_types                         true
% 0.62/1.08  --sat_non_cyclic_types                  false
% 0.62/1.08  --sat_finite_models                     false
% 0.62/1.08  --sat_fm_lemmas                         false
% 0.62/1.08  --sat_fm_prep                           false
% 0.62/1.08  --sat_fm_uc_incr                        true
% 0.62/1.08  --sat_out_model                         small
% 0.62/1.08  --sat_out_clauses                       false
% 0.62/1.08  
% 0.62/1.08  ------ QBF Options
% 0.62/1.08  
% 0.62/1.08  --qbf_mode                              false
% 0.62/1.08  --qbf_elim_univ                         false
% 0.62/1.08  --qbf_dom_inst                          none
% 0.62/1.08  --qbf_dom_pre_inst                      false
% 0.62/1.08  --qbf_sk_in                             false
% 0.62/1.08  --qbf_pred_elim                         true
% 0.62/1.08  --qbf_split                             512
% 0.62/1.08  
% 0.62/1.08  ------ BMC1 Options
% 0.62/1.08  
% 0.62/1.08  --bmc1_incremental                      false
% 0.62/1.08  --bmc1_axioms                           reachable_all
% 0.62/1.08  --bmc1_min_bound                        0
% 0.62/1.08  --bmc1_max_bound                        -1
% 0.62/1.08  --bmc1_max_bound_default                -1
% 0.62/1.08  --bmc1_symbol_reachability              true
% 0.62/1.09  --bmc1_property_lemmas                  false
% 0.62/1.09  --bmc1_k_induction                      false
% 0.62/1.09  --bmc1_non_equiv_states                 false
% 0.62/1.09  --bmc1_deadlock                         false
% 0.62/1.09  --bmc1_ucm                              false
% 0.62/1.09  --bmc1_add_unsat_core                   none
% 0.62/1.09  --bmc1_unsat_core_children              false
% 0.62/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 0.62/1.09  --bmc1_out_stat                         full
% 0.62/1.09  --bmc1_ground_init                      false
% 0.62/1.09  --bmc1_pre_inst_next_state              false
% 0.62/1.09  --bmc1_pre_inst_state                   false
% 0.62/1.09  --bmc1_pre_inst_reach_state             false
% 0.62/1.09  --bmc1_out_unsat_core                   false
% 0.62/1.09  --bmc1_aig_witness_out                  false
% 0.62/1.09  --bmc1_verbose                          false
% 0.62/1.09  --bmc1_dump_clauses_tptp                false
% 0.62/1.09  --bmc1_dump_unsat_core_tptp             false
% 0.62/1.09  --bmc1_dump_file                        -
% 0.62/1.09  --bmc1_ucm_expand_uc_limit              128
% 0.62/1.09  --bmc1_ucm_n_expand_iterations          6
% 0.62/1.09  --bmc1_ucm_extend_mode                  1
% 0.62/1.09  --bmc1_ucm_init_mode                    2
% 0.62/1.09  --bmc1_ucm_cone_mode                    none
% 0.62/1.09  --bmc1_ucm_reduced_relation_type        0
% 0.62/1.09  --bmc1_ucm_relax_model                  4
% 0.62/1.09  --bmc1_ucm_full_tr_after_sat            true
% 0.62/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 0.62/1.09  --bmc1_ucm_layered_model                none
% 0.62/1.09  --bmc1_ucm_max_lemma_size               10
% 0.62/1.09  
% 0.62/1.09  ------ AIG Options
% 0.62/1.09  
% 0.62/1.09  --aig_mode                              false
% 0.62/1.09  
% 0.62/1.09  ------ Instantiation Options
% 0.62/1.09  
% 0.62/1.09  --instantiation_flag                    true
% 0.62/1.09  --inst_sos_flag                         false
% 0.62/1.09  --inst_sos_phase                        true
% 0.62/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.62/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.62/1.09  --inst_lit_sel_side                     none
% 0.62/1.09  --inst_solver_per_active                1400
% 0.62/1.09  --inst_solver_calls_frac                1.
% 0.62/1.09  --inst_passive_queue_type               priority_queues
% 0.62/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.62/1.09  --inst_passive_queues_freq              [25;2]
% 0.62/1.09  --inst_dismatching                      true
% 0.62/1.09  --inst_eager_unprocessed_to_passive     true
% 0.62/1.09  --inst_prop_sim_given                   true
% 0.62/1.09  --inst_prop_sim_new                     false
% 0.62/1.09  --inst_subs_new                         false
% 0.62/1.09  --inst_eq_res_simp                      false
% 0.62/1.09  --inst_subs_given                       false
% 0.62/1.09  --inst_orphan_elimination               true
% 0.62/1.09  --inst_learning_loop_flag               true
% 0.62/1.09  --inst_learning_start                   3000
% 0.62/1.09  --inst_learning_factor                  2
% 0.62/1.09  --inst_start_prop_sim_after_learn       3
% 0.62/1.09  --inst_sel_renew                        solver
% 0.62/1.09  --inst_lit_activity_flag                true
% 0.62/1.09  --inst_restr_to_given                   false
% 0.62/1.09  --inst_activity_threshold               500
% 0.62/1.09  --inst_out_proof                        true
% 0.62/1.09  
% 0.62/1.09  ------ Resolution Options
% 0.62/1.09  
% 0.62/1.09  --resolution_flag                       false
% 0.62/1.09  --res_lit_sel                           adaptive
% 0.62/1.09  --res_lit_sel_side                      none
% 0.62/1.09  --res_ordering                          kbo
% 0.62/1.09  --res_to_prop_solver                    active
% 0.62/1.09  --res_prop_simpl_new                    false
% 0.62/1.09  --res_prop_simpl_given                  true
% 0.62/1.09  --res_passive_queue_type                priority_queues
% 0.62/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.62/1.09  --res_passive_queues_freq               [15;5]
% 0.62/1.09  --res_forward_subs                      full
% 0.62/1.09  --res_backward_subs                     full
% 0.62/1.09  --res_forward_subs_resolution           true
% 0.62/1.09  --res_backward_subs_resolution          true
% 0.62/1.09  --res_orphan_elimination                true
% 0.62/1.09  --res_time_limit                        2.
% 0.62/1.09  --res_out_proof                         true
% 0.62/1.09  
% 0.62/1.09  ------ Superposition Options
% 0.62/1.09  
% 0.62/1.09  --superposition_flag                    true
% 0.62/1.09  --sup_passive_queue_type                priority_queues
% 0.62/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.62/1.09  --sup_passive_queues_freq               [8;1;4]
% 0.62/1.09  --demod_completeness_check              fast
% 0.62/1.09  --demod_use_ground                      true
% 0.62/1.09  --sup_to_prop_solver                    passive
% 0.62/1.09  --sup_prop_simpl_new                    true
% 0.62/1.09  --sup_prop_simpl_given                  true
% 0.62/1.09  --sup_fun_splitting                     false
% 0.62/1.09  --sup_smt_interval                      50000
% 0.62/1.09  
% 0.62/1.09  ------ Superposition Simplification Setup
% 0.62/1.09  
% 0.62/1.09  --sup_indices_passive                   []
% 0.62/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.62/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.62/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.62/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 0.62/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.62/1.09  --sup_full_bw                           [BwDemod]
% 0.62/1.09  --sup_immed_triv                        [TrivRules]
% 0.62/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.62/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.62/1.09  --sup_immed_bw_main                     []
% 0.62/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.62/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 0.62/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.62/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.62/1.09  
% 0.62/1.09  ------ Combination Options
% 0.62/1.09  
% 0.62/1.09  --comb_res_mult                         3
% 0.62/1.09  --comb_sup_mult                         2
% 0.62/1.09  --comb_inst_mult                        10
% 0.62/1.09  
% 0.62/1.09  ------ Debug Options
% 0.62/1.09  
% 0.62/1.09  --dbg_backtrace                         false
% 0.62/1.09  --dbg_dump_prop_clauses                 false
% 0.62/1.09  --dbg_dump_prop_clauses_file            -
% 0.62/1.09  --dbg_out_stat                          false
% 0.62/1.09  
% 0.62/1.09  
% 0.62/1.09  
% 0.62/1.09  
% 0.62/1.09  ------ Proving...
% 0.62/1.09  
% 0.62/1.09  
% 0.62/1.09  % SZS status Theorem for theBenchmark.p
% 0.62/1.09  
% 0.62/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 0.62/1.09  
% 0.62/1.09  fof(f21,conjecture,(
% 0.62/1.09    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f22,negated_conjecture,(
% 0.62/1.09    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.62/1.09    inference(negated_conjecture,[],[f21])).
% 0.62/1.09  
% 0.62/1.09  fof(f49,plain,(
% 0.62/1.09    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.62/1.09    inference(ennf_transformation,[],[f22])).
% 0.62/1.09  
% 0.62/1.09  fof(f50,plain,(
% 0.62/1.09    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.62/1.09    inference(flattening,[],[f49])).
% 0.62/1.09  
% 0.62/1.09  fof(f58,plain,(
% 0.62/1.09    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.62/1.09    introduced(choice_axiom,[])).
% 0.62/1.09  
% 0.62/1.09  fof(f59,plain,(
% 0.62/1.09    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.62/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f58])).
% 0.62/1.09  
% 0.62/1.09  fof(f99,plain,(
% 0.62/1.09    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.62/1.09    inference(cnf_transformation,[],[f59])).
% 0.62/1.09  
% 0.62/1.09  fof(f5,axiom,(
% 0.62/1.09    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f26,plain,(
% 0.62/1.09    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.62/1.09    inference(ennf_transformation,[],[f5])).
% 0.62/1.09  
% 0.62/1.09  fof(f68,plain,(
% 0.62/1.09    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f26])).
% 0.62/1.09  
% 0.62/1.09  fof(f1,axiom,(
% 0.62/1.09    v1_xboole_0(k1_xboole_0)),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f60,plain,(
% 0.62/1.09    v1_xboole_0(k1_xboole_0)),
% 0.62/1.09    inference(cnf_transformation,[],[f1])).
% 0.62/1.09  
% 0.62/1.09  fof(f17,axiom,(
% 0.62/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f44,plain,(
% 0.62/1.09    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(ennf_transformation,[],[f17])).
% 0.62/1.09  
% 0.62/1.09  fof(f83,plain,(
% 0.62/1.09    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.62/1.09    inference(cnf_transformation,[],[f44])).
% 0.62/1.09  
% 0.62/1.09  fof(f101,plain,(
% 0.62/1.09    k2_relset_1(sK1,sK2,sK3) = sK2),
% 0.62/1.09    inference(cnf_transformation,[],[f59])).
% 0.62/1.09  
% 0.62/1.09  fof(f8,axiom,(
% 0.62/1.09    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f29,plain,(
% 0.62/1.09    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.62/1.09    inference(ennf_transformation,[],[f8])).
% 0.62/1.09  
% 0.62/1.09  fof(f30,plain,(
% 0.62/1.09    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.62/1.09    inference(flattening,[],[f29])).
% 0.62/1.09  
% 0.62/1.09  fof(f72,plain,(
% 0.62/1.09    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f30])).
% 0.62/1.09  
% 0.62/1.09  fof(f15,axiom,(
% 0.62/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f42,plain,(
% 0.62/1.09    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(ennf_transformation,[],[f15])).
% 0.62/1.09  
% 0.62/1.09  fof(f81,plain,(
% 0.62/1.09    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.62/1.09    inference(cnf_transformation,[],[f42])).
% 0.62/1.09  
% 0.62/1.09  fof(f18,axiom,(
% 0.62/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f45,plain,(
% 0.62/1.09    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(ennf_transformation,[],[f18])).
% 0.62/1.09  
% 0.62/1.09  fof(f46,plain,(
% 0.62/1.09    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(flattening,[],[f45])).
% 0.62/1.09  
% 0.62/1.09  fof(f55,plain,(
% 0.62/1.09    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(nnf_transformation,[],[f46])).
% 0.62/1.09  
% 0.62/1.09  fof(f84,plain,(
% 0.62/1.09    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.62/1.09    inference(cnf_transformation,[],[f55])).
% 0.62/1.09  
% 0.62/1.09  fof(f98,plain,(
% 0.62/1.09    v1_funct_2(sK3,sK1,sK2)),
% 0.62/1.09    inference(cnf_transformation,[],[f59])).
% 0.62/1.09  
% 0.62/1.09  fof(f16,axiom,(
% 0.62/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f43,plain,(
% 0.62/1.09    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(ennf_transformation,[],[f16])).
% 0.62/1.09  
% 0.62/1.09  fof(f82,plain,(
% 0.62/1.09    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.62/1.09    inference(cnf_transformation,[],[f43])).
% 0.62/1.09  
% 0.62/1.09  fof(f14,axiom,(
% 0.62/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f40,plain,(
% 0.62/1.09    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.62/1.09    inference(ennf_transformation,[],[f14])).
% 0.62/1.09  
% 0.62/1.09  fof(f41,plain,(
% 0.62/1.09    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.62/1.09    inference(flattening,[],[f40])).
% 0.62/1.09  
% 0.62/1.09  fof(f80,plain,(
% 0.62/1.09    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f41])).
% 0.62/1.09  
% 0.62/1.09  fof(f100,plain,(
% 0.62/1.09    v2_funct_1(sK3)),
% 0.62/1.09    inference(cnf_transformation,[],[f59])).
% 0.62/1.09  
% 0.62/1.09  fof(f97,plain,(
% 0.62/1.09    v1_funct_1(sK3)),
% 0.62/1.09    inference(cnf_transformation,[],[f59])).
% 0.62/1.09  
% 0.62/1.09  fof(f20,axiom,(
% 0.62/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f47,plain,(
% 0.62/1.09    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.62/1.09    inference(ennf_transformation,[],[f20])).
% 0.62/1.09  
% 0.62/1.09  fof(f48,plain,(
% 0.62/1.09    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.62/1.09    inference(flattening,[],[f47])).
% 0.62/1.09  
% 0.62/1.09  fof(f96,plain,(
% 0.62/1.09    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f48])).
% 0.62/1.09  
% 0.62/1.09  fof(f79,plain,(
% 0.62/1.09    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f41])).
% 0.62/1.09  
% 0.62/1.09  fof(f10,axiom,(
% 0.62/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f32,plain,(
% 0.62/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.62/1.09    inference(ennf_transformation,[],[f10])).
% 0.62/1.09  
% 0.62/1.09  fof(f33,plain,(
% 0.62/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.62/1.09    inference(flattening,[],[f32])).
% 0.62/1.09  
% 0.62/1.09  fof(f75,plain,(
% 0.62/1.09    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f33])).
% 0.62/1.09  
% 0.62/1.09  fof(f74,plain,(
% 0.62/1.09    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f33])).
% 0.62/1.09  
% 0.62/1.09  fof(f95,plain,(
% 0.62/1.09    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f48])).
% 0.62/1.09  
% 0.62/1.09  fof(f102,plain,(
% 0.62/1.09    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.62/1.09    inference(cnf_transformation,[],[f59])).
% 0.62/1.09  
% 0.62/1.09  fof(f2,axiom,(
% 0.62/1.09    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f25,plain,(
% 0.62/1.09    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.62/1.09    inference(ennf_transformation,[],[f2])).
% 0.62/1.09  
% 0.62/1.09  fof(f61,plain,(
% 0.62/1.09    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f25])).
% 0.62/1.09  
% 0.62/1.09  fof(f86,plain,(
% 0.62/1.09    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.62/1.09    inference(cnf_transformation,[],[f55])).
% 0.62/1.09  
% 0.62/1.09  fof(f19,axiom,(
% 0.62/1.09    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f23,plain,(
% 0.62/1.09    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(pure_predicate_removal,[],[f19])).
% 0.62/1.09  
% 0.62/1.09  fof(f24,plain,(
% 0.62/1.09    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(pure_predicate_removal,[],[f23])).
% 0.62/1.09  
% 0.62/1.09  fof(f56,plain,(
% 0.62/1.09    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.62/1.09    introduced(choice_axiom,[])).
% 0.62/1.09  
% 0.62/1.09  fof(f57,plain,(
% 0.62/1.09    ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.62/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f56])).
% 0.62/1.09  
% 0.62/1.09  fof(f91,plain,(
% 0.62/1.09    ( ! [X0,X1] : (v1_relat_1(sK0(X0,X1))) )),
% 0.62/1.09    inference(cnf_transformation,[],[f57])).
% 0.62/1.09  
% 0.62/1.09  fof(f9,axiom,(
% 0.62/1.09    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f31,plain,(
% 0.62/1.09    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.62/1.09    inference(ennf_transformation,[],[f9])).
% 0.62/1.09  
% 0.62/1.09  fof(f73,plain,(
% 0.62/1.09    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f31])).
% 0.62/1.09  
% 0.62/1.09  fof(f4,axiom,(
% 0.62/1.09    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.62/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.62/1.09  
% 0.62/1.09  fof(f53,plain,(
% 0.62/1.09    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.62/1.09    inference(nnf_transformation,[],[f4])).
% 0.62/1.09  
% 0.62/1.09  fof(f54,plain,(
% 0.62/1.09    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.62/1.09    inference(flattening,[],[f53])).
% 0.62/1.09  
% 0.62/1.09  fof(f66,plain,(
% 0.62/1.09    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.62/1.09    inference(cnf_transformation,[],[f54])).
% 0.62/1.09  
% 0.62/1.09  fof(f106,plain,(
% 0.62/1.09    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.62/1.09    inference(equality_resolution,[],[f66])).
% 0.62/1.09  
% 0.62/1.09  fof(f90,plain,(
% 0.62/1.09    ( ! [X0,X1] : (m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.62/1.09    inference(cnf_transformation,[],[f57])).
% 0.62/1.09  
% 0.62/1.09  fof(f71,plain,(
% 0.62/1.09    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.62/1.09    inference(cnf_transformation,[],[f30])).
% 0.62/1.09  
% 0.62/1.09  fof(f67,plain,(
% 0.62/1.09    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.62/1.09    inference(cnf_transformation,[],[f54])).
% 0.62/1.09  
% 0.62/1.09  fof(f105,plain,(
% 0.62/1.09    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.62/1.09    inference(equality_resolution,[],[f67])).
% 0.62/1.09  
% 0.62/1.09  cnf(c_40,negated_conjecture,
% 0.62/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 0.62/1.09      inference(cnf_transformation,[],[f99]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2096,plain,
% 0.62/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_8,plain,
% 0.62/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.62/1.09      | ~ v1_xboole_0(X1)
% 0.62/1.09      | v1_xboole_0(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f68]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2112,plain,
% 0.62/1.09      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.62/1.09      | v1_xboole_0(X1) != iProver_top
% 0.62/1.09      | v1_xboole_0(X0) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5221,plain,
% 0.62/1.09      ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 0.62/1.09      | v1_xboole_0(sK3) = iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_2096,c_2112]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_0,plain,
% 0.62/1.09      ( v1_xboole_0(k1_xboole_0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f60]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_143,plain,
% 0.62/1.09      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1460,plain,
% 0.62/1.09      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.62/1.09      theory(equality) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3263,plain,
% 0.62/1.09      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_1460]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3264,plain,
% 0.62/1.09      ( sK3 != X0
% 0.62/1.09      | v1_xboole_0(X0) != iProver_top
% 0.62/1.09      | v1_xboole_0(sK3) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_3263]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3266,plain,
% 0.62/1.09      ( sK3 != k1_xboole_0
% 0.62/1.09      | v1_xboole_0(sK3) = iProver_top
% 0.62/1.09      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_3264]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_23,plain,
% 0.62/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.62/1.09      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f83]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2101,plain,
% 0.62/1.09      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.62/1.09      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3940,plain,
% 0.62/1.09      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_2096,c_2101]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_38,negated_conjecture,
% 0.62/1.09      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 0.62/1.09      inference(cnf_transformation,[],[f101]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3956,plain,
% 0.62/1.09      ( k2_relat_1(sK3) = sK2 ),
% 0.62/1.09      inference(light_normalisation,[status(thm)],[c_3940,c_38]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_11,plain,
% 0.62/1.09      ( ~ v1_relat_1(X0)
% 0.62/1.09      | k2_relat_1(X0) != k1_xboole_0
% 0.62/1.09      | k1_xboole_0 = X0 ),
% 0.62/1.09      inference(cnf_transformation,[],[f72]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2109,plain,
% 0.62/1.09      ( k2_relat_1(X0) != k1_xboole_0
% 0.62/1.09      | k1_xboole_0 = X0
% 0.62/1.09      | v1_relat_1(X0) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4035,plain,
% 0.62/1.09      ( sK2 != k1_xboole_0
% 0.62/1.09      | sK3 = k1_xboole_0
% 0.62/1.09      | v1_relat_1(sK3) != iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_3956,c_2109]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_45,plain,
% 0.62/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_21,plain,
% 0.62/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.62/1.09      | v1_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f81]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2435,plain,
% 0.62/1.09      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.62/1.09      | v1_relat_1(sK3) ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_21]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2436,plain,
% 0.62/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 0.62/1.09      | v1_relat_1(sK3) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_2435]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4923,plain,
% 0.62/1.09      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_4035,c_45,c_2436]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4924,plain,
% 0.62/1.09      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 0.62/1.09      inference(renaming,[status(thm)],[c_4923]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_29,plain,
% 0.62/1.09      ( ~ v1_funct_2(X0,X1,X2)
% 0.62/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.62/1.09      | k1_relset_1(X1,X2,X0) = X1
% 0.62/1.09      | k1_xboole_0 = X2 ),
% 0.62/1.09      inference(cnf_transformation,[],[f84]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_41,negated_conjecture,
% 0.62/1.09      ( v1_funct_2(sK3,sK1,sK2) ),
% 0.62/1.09      inference(cnf_transformation,[],[f98]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1341,plain,
% 0.62/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.62/1.09      | k1_relset_1(X1,X2,X0) = X1
% 0.62/1.09      | sK1 != X1
% 0.62/1.09      | sK2 != X2
% 0.62/1.09      | sK3 != X0
% 0.62/1.09      | k1_xboole_0 = X2 ),
% 0.62/1.09      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1342,plain,
% 0.62/1.09      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.62/1.09      | k1_relset_1(sK1,sK2,sK3) = sK1
% 0.62/1.09      | k1_xboole_0 = sK2 ),
% 0.62/1.09      inference(unflattening,[status(thm)],[c_1341]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1344,plain,
% 0.62/1.09      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_1342,c_40]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_22,plain,
% 0.62/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.62/1.09      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f82]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2102,plain,
% 0.62/1.09      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.62/1.09      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4756,plain,
% 0.62/1.09      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_2096,c_2102]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4826,plain,
% 0.62/1.09      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_1344,c_4756]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2103,plain,
% 0.62/1.09      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.62/1.09      | v1_relat_1(X0) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3540,plain,
% 0.62/1.09      ( v1_relat_1(sK3) = iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_2096,c_2103]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_19,plain,
% 0.62/1.09      ( ~ v2_funct_1(X0)
% 0.62/1.09      | ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_relat_1(X0)
% 0.62/1.09      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f80]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_39,negated_conjecture,
% 0.62/1.09      ( v2_funct_1(sK3) ),
% 0.62/1.09      inference(cnf_transformation,[],[f100]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_469,plain,
% 0.62/1.09      ( ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_relat_1(X0)
% 0.62/1.09      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 0.62/1.09      | sK3 != X0 ),
% 0.62/1.09      inference(resolution_lifted,[status(thm)],[c_19,c_39]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_470,plain,
% 0.62/1.09      ( ~ v1_funct_1(sK3)
% 0.62/1.09      | ~ v1_relat_1(sK3)
% 0.62/1.09      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 0.62/1.09      inference(unflattening,[status(thm)],[c_469]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_42,negated_conjecture,
% 0.62/1.09      ( v1_funct_1(sK3) ),
% 0.62/1.09      inference(cnf_transformation,[],[f97]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_472,plain,
% 0.62/1.09      ( ~ v1_relat_1(sK3)
% 0.62/1.09      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_470,c_42]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2092,plain,
% 0.62/1.09      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 0.62/1.09      | v1_relat_1(sK3) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3558,plain,
% 0.62/1.09      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_3540,c_2092]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_34,plain,
% 0.62/1.09      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 0.62/1.09      | ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f96]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2097,plain,
% 0.62/1.09      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 0.62/1.09      | v1_funct_1(X0) != iProver_top
% 0.62/1.09      | v1_relat_1(X0) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3613,plain,
% 0.62/1.09      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 0.62/1.09      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_3558,c_2097]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_20,plain,
% 0.62/1.09      ( ~ v2_funct_1(X0)
% 0.62/1.09      | ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_relat_1(X0)
% 0.62/1.09      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f79]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_455,plain,
% 0.62/1.09      ( ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_relat_1(X0)
% 0.62/1.09      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 0.62/1.09      | sK3 != X0 ),
% 0.62/1.09      inference(resolution_lifted,[status(thm)],[c_20,c_39]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_456,plain,
% 0.62/1.09      ( ~ v1_funct_1(sK3)
% 0.62/1.09      | ~ v1_relat_1(sK3)
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 0.62/1.09      inference(unflattening,[status(thm)],[c_455]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_458,plain,
% 0.62/1.09      ( ~ v1_relat_1(sK3)
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_456,c_42]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2093,plain,
% 0.62/1.09      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 0.62/1.09      | v1_relat_1(sK3) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3557,plain,
% 0.62/1.09      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_3540,c_2093]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3614,plain,
% 0.62/1.09      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 0.62/1.09      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(light_normalisation,[status(thm)],[c_3613,c_3557]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_43,plain,
% 0.62/1.09      ( v1_funct_1(sK3) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_14,plain,
% 0.62/1.09      ( ~ v1_funct_1(X0)
% 0.62/1.09      | v1_funct_1(k2_funct_1(X0))
% 0.62/1.09      | ~ v1_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f75]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2556,plain,
% 0.62/1.09      ( v1_funct_1(k2_funct_1(sK3))
% 0.62/1.09      | ~ v1_funct_1(sK3)
% 0.62/1.09      | ~ v1_relat_1(sK3) ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_14]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2557,plain,
% 0.62/1.09      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 0.62/1.09      | v1_funct_1(sK3) != iProver_top
% 0.62/1.09      | v1_relat_1(sK3) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_2556]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_15,plain,
% 0.62/1.09      ( ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_relat_1(X0)
% 0.62/1.09      | v1_relat_1(k2_funct_1(X0)) ),
% 0.62/1.09      inference(cnf_transformation,[],[f74]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2555,plain,
% 0.62/1.09      ( ~ v1_funct_1(sK3)
% 0.62/1.09      | v1_relat_1(k2_funct_1(sK3))
% 0.62/1.09      | ~ v1_relat_1(sK3) ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_15]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2559,plain,
% 0.62/1.09      ( v1_funct_1(sK3) != iProver_top
% 0.62/1.09      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 0.62/1.09      | v1_relat_1(sK3) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_2555]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3785,plain,
% 0.62/1.09      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_3614,c_43,c_45,c_2436,c_2557,c_2559]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4009,plain,
% 0.62/1.09      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_3956,c_3785]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5092,plain,
% 0.62/1.09      ( sK2 = k1_xboole_0
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_4826,c_4009]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_35,plain,
% 0.62/1.09      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 0.62/1.09      | ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_relat_1(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f95]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_37,negated_conjecture,
% 0.62/1.09      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 0.62/1.09      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 0.62/1.09      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 0.62/1.09      inference(cnf_transformation,[],[f102]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1365,plain,
% 0.62/1.09      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 0.62/1.09      | ~ v1_funct_1(X0)
% 0.62/1.09      | ~ v1_funct_1(k2_funct_1(sK3))
% 0.62/1.09      | ~ v1_relat_1(X0)
% 0.62/1.09      | k2_funct_1(sK3) != X0
% 0.62/1.09      | k2_relat_1(X0) != sK1
% 0.62/1.09      | k1_relat_1(X0) != sK2 ),
% 0.62/1.09      inference(resolution_lifted,[status(thm)],[c_35,c_37]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1366,plain,
% 0.62/1.09      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 0.62/1.09      | ~ v1_funct_1(k2_funct_1(sK3))
% 0.62/1.09      | ~ v1_relat_1(k2_funct_1(sK3))
% 0.62/1.09      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 0.62/1.09      inference(unflattening,[status(thm)],[c_1365]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1378,plain,
% 0.62/1.09      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 0.62/1.09      | ~ v1_funct_1(k2_funct_1(sK3))
% 0.62/1.09      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 0.62/1.09      inference(forward_subsumption_resolution,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_1366,c_21]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2082,plain,
% 0.62/1.09      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1367,plain,
% 0.62/1.09      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 0.62/1.09      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_1366]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2742,plain,
% 0.62/1.09      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 0.62/1.09      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_2082,c_43,c_45,c_1367,c_2436,c_2557,c_2559]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2743,plain,
% 0.62/1.09      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 0.62/1.09      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(renaming,[status(thm)],[c_2742]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3608,plain,
% 0.62/1.09      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 0.62/1.09      | k2_relat_1(sK3) != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_3557,c_2743]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3698,plain,
% 0.62/1.09      ( k2_relat_1(sK3) != sK2
% 0.62/1.09      | k1_relat_1(sK3) != sK1
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(light_normalisation,[status(thm)],[c_3608,c_3558]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4010,plain,
% 0.62/1.09      ( k1_relat_1(sK3) != sK1
% 0.62/1.09      | sK2 != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_3956,c_3698]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4026,plain,
% 0.62/1.09      ( k1_relat_1(sK3) != sK1
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(equality_resolution_simp,[status(thm)],[c_4010]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5157,plain,
% 0.62/1.09      ( sK2 = k1_xboole_0
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_4826,c_4026]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5318,plain,
% 0.62/1.09      ( v1_xboole_0(sK3) = iProver_top ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_5221,c_143,c_3266,c_4924,c_5092,c_5157]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1,plain,
% 0.62/1.09      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 0.62/1.09      inference(cnf_transformation,[],[f61]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2115,plain,
% 0.62/1.09      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5324,plain,
% 0.62/1.09      ( sK3 = k1_xboole_0 ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_5318,c_2115]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_27,plain,
% 0.62/1.09      ( v1_funct_2(X0,X1,X2)
% 0.62/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.62/1.09      | k1_relset_1(X1,X2,X0) != X1
% 0.62/1.09      | k1_xboole_0 = X2 ),
% 0.62/1.09      inference(cnf_transformation,[],[f86]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1325,plain,
% 0.62/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.62/1.09      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 0.62/1.09      | ~ v1_funct_1(k2_funct_1(sK3))
% 0.62/1.09      | k1_relset_1(X1,X2,X0) != X1
% 0.62/1.09      | k2_funct_1(sK3) != X0
% 0.62/1.09      | sK1 != X2
% 0.62/1.09      | sK2 != X1
% 0.62/1.09      | k1_xboole_0 = X2 ),
% 0.62/1.09      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1326,plain,
% 0.62/1.09      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 0.62/1.09      | ~ v1_funct_1(k2_funct_1(sK3))
% 0.62/1.09      | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 0.62/1.09      | k1_xboole_0 = sK1 ),
% 0.62/1.09      inference(unflattening,[status(thm)],[c_1325]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2084,plain,
% 0.62/1.09      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 0.62/1.09      | k1_xboole_0 = sK1
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1327,plain,
% 0.62/1.09      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 0.62/1.09      | k1_xboole_0 = sK1
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2723,plain,
% 0.62/1.09      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | k1_xboole_0 = sK1
% 0.62/1.09      | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2 ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_2084,c_43,c_45,c_1327,c_2436,c_2557]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2724,plain,
% 0.62/1.09      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 0.62/1.09      | k1_xboole_0 = sK1
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(renaming,[status(thm)],[c_2723]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5353,plain,
% 0.62/1.09      ( k1_relset_1(sK2,sK1,k2_funct_1(k1_xboole_0)) != sK2
% 0.62/1.09      | sK1 = k1_xboole_0
% 0.62/1.09      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_5324,c_2724]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_32,plain,
% 0.62/1.09      ( v1_relat_1(sK0(X0,X1)) ),
% 0.62/1.09      inference(cnf_transformation,[],[f91]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_58,plain,
% 0.62/1.09      ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_60,plain,
% 0.62/1.09      ( v1_relat_1(sK0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_58]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_109,plain,
% 0.62/1.09      ( v1_funct_1(X0) != iProver_top
% 0.62/1.09      | v1_relat_1(X0) != iProver_top
% 0.62/1.09      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_111,plain,
% 0.62/1.09      ( v1_funct_1(k1_xboole_0) != iProver_top
% 0.62/1.09      | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 0.62/1.09      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_109]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_112,plain,
% 0.62/1.09      ( v1_funct_1(X0) != iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 0.62/1.09      | v1_relat_1(X0) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_114,plain,
% 0.62/1.09      ( v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 0.62/1.09      | v1_funct_1(k1_xboole_0) != iProver_top
% 0.62/1.09      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_112]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_13,plain,
% 0.62/1.09      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 0.62/1.09      inference(cnf_transformation,[],[f73]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_115,plain,
% 0.62/1.09      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_117,plain,
% 0.62/1.09      ( v1_funct_1(k1_xboole_0) = iProver_top
% 0.62/1.09      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_115]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_6,plain,
% 0.62/1.09      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.62/1.09      inference(cnf_transformation,[],[f106]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_132,plain,
% 0.62/1.09      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_6]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_33,plain,
% 0.62/1.09      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.62/1.09      inference(cnf_transformation,[],[f90]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_514,plain,
% 0.62/1.09      ( ~ v1_xboole_0(X0)
% 0.62/1.09      | v1_xboole_0(X1)
% 0.62/1.09      | sK0(X2,X3) != X1
% 0.62/1.09      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(X0) ),
% 0.62/1.09      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_515,plain,
% 0.62/1.09      ( ~ v1_xboole_0(X0)
% 0.62/1.09      | v1_xboole_0(sK0(X1,X2))
% 0.62/1.09      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X0) ),
% 0.62/1.09      inference(unflattening,[status(thm)],[c_514]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_516,plain,
% 0.62/1.09      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2)
% 0.62/1.09      | v1_xboole_0(X2) != iProver_top
% 0.62/1.09      | v1_xboole_0(sK0(X0,X1)) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_518,plain,
% 0.62/1.09      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 0.62/1.09      | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0)) = iProver_top
% 0.62/1.09      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_516]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1468,plain,
% 0.62/1.09      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 0.62/1.09      theory(equality) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2545,plain,
% 0.62/1.09      ( v1_relat_1(X0) | ~ v1_relat_1(sK0(X1,X2)) | X0 != sK0(X1,X2) ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_1468]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2546,plain,
% 0.62/1.09      ( X0 != sK0(X1,X2)
% 0.62/1.09      | v1_relat_1(X0) = iProver_top
% 0.62/1.09      | v1_relat_1(sK0(X1,X2)) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_2545]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2548,plain,
% 0.62/1.09      ( k1_xboole_0 != sK0(k1_xboole_0,k1_xboole_0)
% 0.62/1.09      | v1_relat_1(sK0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 0.62/1.09      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_2546]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3173,plain,
% 0.62/1.09      ( ~ v1_xboole_0(sK0(X0,X1)) | k1_xboole_0 = sK0(X0,X1) ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_1]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3176,plain,
% 0.62/1.09      ( k1_xboole_0 = sK0(X0,X1)
% 0.62/1.09      | v1_xboole_0(sK0(X0,X1)) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_3173]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3178,plain,
% 0.62/1.09      ( k1_xboole_0 = sK0(k1_xboole_0,k1_xboole_0)
% 0.62/1.09      | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_3176]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1459,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2661,plain,
% 0.62/1.09      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_1459]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3814,plain,
% 0.62/1.09      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_2661]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_3815,plain,
% 0.62/1.09      ( sK1 = sK2 | sK1 != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_3814]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1463,plain,
% 0.62/1.09      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 0.62/1.09      theory(equality) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4873,plain,
% 0.62/1.09      ( k2_zfmisc_1(X0,X1) != X2
% 0.62/1.09      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2) ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_1463]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4878,plain,
% 0.62/1.09      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 0.62/1.09      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0) ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_4873]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_1384,plain,
% 0.62/1.09      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 0.62/1.09      | ~ v1_funct_1(k2_funct_1(sK3))
% 0.62/1.09      | k2_funct_1(sK3) != sK3
% 0.62/1.09      | sK1 != sK2 ),
% 0.62/1.09      inference(resolution_lifted,[status(thm)],[c_37,c_41]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2081,plain,
% 0.62/1.09      ( k2_funct_1(sK3) != sK3
% 0.62/1.09      | sK1 != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5355,plain,
% 0.62/1.09      ( k2_funct_1(k1_xboole_0) != k1_xboole_0
% 0.62/1.09      | sK1 != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 0.62/1.09      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_5324,c_2081]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5358,plain,
% 0.62/1.09      ( k1_relset_1(sK1,sK2,k1_xboole_0) = sK1 | sK2 = k1_xboole_0 ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_5324,c_1344]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5569,plain,
% 0.62/1.09      ( sK2 = k1_xboole_0 ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_5358,c_5092,c_5157]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4014,plain,
% 0.62/1.09      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_3956,c_3557]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5345,plain,
% 0.62/1.09      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK2 ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_5324,c_4014]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_6166,plain,
% 0.62/1.09      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 0.62/1.09      inference(light_normalisation,[status(thm)],[c_5345,c_5569]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_12,plain,
% 0.62/1.09      ( ~ v1_relat_1(X0)
% 0.62/1.09      | k1_relat_1(X0) != k1_xboole_0
% 0.62/1.09      | k1_xboole_0 = X0 ),
% 0.62/1.09      inference(cnf_transformation,[],[f71]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2108,plain,
% 0.62/1.09      ( k1_relat_1(X0) != k1_xboole_0
% 0.62/1.09      | k1_xboole_0 = X0
% 0.62/1.09      | v1_relat_1(X0) != iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_6169,plain,
% 0.62/1.09      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 0.62/1.09      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_6166,c_2108]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_7255,plain,
% 0.62/1.09      ( k1_relset_1(sK2,sK1,k2_funct_1(k1_xboole_0)) != sK2
% 0.62/1.09      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_5353,c_60,c_111,c_114,c_117,c_132,c_143,c_518,c_2548,
% 0.62/1.09                 c_3178,c_3815,c_4878,c_5092,c_5157,c_5355,c_6169]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5224,plain,
% 0.62/1.09      ( v1_xboole_0(k2_zfmisc_1(sK2,k1_relat_1(sK3))) != iProver_top
% 0.62/1.09      | v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_4009,c_2112]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2631,plain,
% 0.62/1.09      ( ~ v1_xboole_0(X0)
% 0.62/1.09      | v1_xboole_0(k2_funct_1(sK3))
% 0.62/1.09      | k2_funct_1(sK3) != X0 ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_1460]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2632,plain,
% 0.62/1.09      ( k2_funct_1(sK3) != X0
% 0.62/1.09      | v1_xboole_0(X0) != iProver_top
% 0.62/1.09      | v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
% 0.62/1.09      inference(predicate_to_equality,[status(thm)],[c_2631]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_2634,plain,
% 0.62/1.09      ( k2_funct_1(sK3) != k1_xboole_0
% 0.62/1.09      | v1_xboole_0(k2_funct_1(sK3)) = iProver_top
% 0.62/1.09      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.62/1.09      inference(instantiation,[status(thm)],[c_2632]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4064,plain,
% 0.62/1.09      ( k2_funct_1(sK3) = k1_xboole_0
% 0.62/1.09      | sK2 != k1_xboole_0
% 0.62/1.09      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_4014,c_2108]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4076,plain,
% 0.62/1.09      ( ~ v1_relat_1(k2_funct_1(sK3))
% 0.62/1.09      | k2_funct_1(sK3) = k1_xboole_0
% 0.62/1.09      | sK2 != k1_xboole_0 ),
% 0.62/1.09      inference(predicate_to_equality_rev,[status(thm)],[c_4064]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_6721,plain,
% 0.62/1.09      ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
% 0.62/1.09      inference(global_propositional_subsumption,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_5224,c_42,c_40,c_143,c_2435,c_2555,c_2634,c_4076,
% 0.62/1.09                 c_5092,c_5157]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_6725,plain,
% 0.62/1.09      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 0.62/1.09      inference(light_normalisation,[status(thm)],[c_6721,c_5324]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_6729,plain,
% 0.62/1.09      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_6725,c_2115]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_7259,plain,
% 0.62/1.09      ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0
% 0.62/1.09      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 0.62/1.09      inference(light_normalisation,[status(thm)],[c_7255,c_5569,c_6729]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5359,plain,
% 0.62/1.09      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_5324,c_2096]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5572,plain,
% 0.62/1.09      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_5569,c_5359]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5,plain,
% 0.62/1.09      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.62/1.09      inference(cnf_transformation,[],[f105]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5580,plain,
% 0.62/1.09      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_5572,c_5]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_4759,plain,
% 0.62/1.09      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 0.62/1.09      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_6,c_2102]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_5811,plain,
% 0.62/1.09      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 0.62/1.09      inference(superposition,[status(thm)],[c_5580,c_4759]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_7260,plain,
% 0.62/1.09      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 0.62/1.09      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_7259,c_6,c_5811]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_7263,plain,
% 0.62/1.09      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 0.62/1.09      inference(forward_subsumption_resolution,
% 0.62/1.09                [status(thm)],
% 0.62/1.09                [c_7260,c_5580]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(c_6916,plain,
% 0.62/1.09      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.62/1.09      inference(demodulation,[status(thm)],[c_6729,c_6166]) ).
% 0.62/1.09  
% 0.62/1.09  cnf(contradiction,plain,
% 0.62/1.09      ( $false ),
% 0.62/1.09      inference(minisat,[status(thm)],[c_7263,c_6916]) ).
% 0.62/1.09  
% 0.62/1.09  
% 0.62/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 0.62/1.09  
% 0.62/1.09  ------                               Statistics
% 0.62/1.09  
% 0.62/1.09  ------ General
% 0.62/1.09  
% 0.62/1.09  abstr_ref_over_cycles:                  0
% 0.62/1.09  abstr_ref_under_cycles:                 0
% 0.62/1.09  gc_basic_clause_elim:                   0
% 0.62/1.09  forced_gc_time:                         0
% 0.62/1.09  parsing_time:                           0.01
% 0.62/1.09  unif_index_cands_time:                  0.
% 0.62/1.09  unif_index_add_time:                    0.
% 0.62/1.09  orderings_time:                         0.
% 0.62/1.09  out_proof_time:                         0.052
% 0.62/1.09  total_time:                             0.474
% 0.62/1.09  num_of_symbols:                         52
% 0.62/1.09  num_of_terms:                           5187
% 0.62/1.09  
% 0.62/1.09  ------ Preprocessing
% 0.62/1.09  
% 0.62/1.09  num_of_splits:                          0
% 2.36/1.10  num_of_split_atoms:                     0
% 2.36/1.10  num_of_reused_defs:                     0
% 2.36/1.10  num_eq_ax_congr_red:                    6
% 2.36/1.10  num_of_sem_filtered_clauses:            1
% 2.36/1.10  num_of_subtypes:                        0
% 2.36/1.10  monotx_restored_types:                  0
% 2.36/1.10  sat_num_of_epr_types:                   0
% 2.36/1.10  sat_num_of_non_cyclic_types:            0
% 2.36/1.10  sat_guarded_non_collapsed_types:        0
% 2.36/1.10  num_pure_diseq_elim:                    0
% 2.36/1.10  simp_replaced_by:                       0
% 2.36/1.10  res_preprocessed:                       164
% 2.36/1.10  prep_upred:                             0
% 2.36/1.10  prep_unflattend:                        85
% 2.36/1.10  smt_new_axioms:                         0
% 2.36/1.10  pred_elim_cands:                        7
% 2.36/1.10  pred_elim:                              2
% 2.36/1.10  pred_elim_cl:                           -3
% 2.36/1.10  pred_elim_cycles:                       4
% 2.36/1.10  merged_defs:                            0
% 2.36/1.10  merged_defs_ncl:                        0
% 2.36/1.10  bin_hyper_res:                          0
% 2.36/1.10  prep_cycles:                            3
% 2.36/1.10  pred_elim_time:                         0.041
% 2.36/1.10  splitting_time:                         0.
% 2.36/1.10  sem_filter_time:                        0.
% 2.36/1.10  monotx_time:                            0.003
% 2.36/1.10  subtype_inf_time:                       0.
% 2.36/1.10  
% 2.36/1.10  ------ Problem properties
% 2.36/1.10  
% 2.36/1.10  clauses:                                44
% 2.36/1.10  conjectures:                            3
% 2.36/1.10  epr:                                    6
% 2.36/1.10  horn:                                   38
% 2.36/1.10  ground:                                 15
% 2.36/1.10  unary:                                  11
% 2.36/1.10  binary:                                 13
% 2.36/1.10  lits:                                   109
% 2.36/1.10  lits_eq:                                49
% 2.36/1.10  fd_pure:                                0
% 2.36/1.10  fd_pseudo:                              0
% 2.36/1.10  fd_cond:                                5
% 2.36/1.10  fd_pseudo_cond:                         1
% 2.36/1.10  ac_symbols:                             0
% 2.36/1.10  
% 2.36/1.10  ------ Propositional Solver
% 2.36/1.10  
% 2.36/1.10  prop_solver_calls:                      24
% 2.36/1.10  prop_fast_solver_calls:                 1309
% 2.36/1.10  smt_solver_calls:                       0
% 2.36/1.10  smt_fast_solver_calls:                  0
% 2.36/1.10  prop_num_of_clauses:                    2502
% 2.36/1.10  prop_preprocess_simplified:             6793
% 2.36/1.10  prop_fo_subsumed:                       36
% 2.36/1.10  prop_solver_time:                       0.
% 2.36/1.10  smt_solver_time:                        0.
% 2.36/1.10  smt_fast_solver_time:                   0.
% 2.36/1.10  prop_fast_solver_time:                  0.
% 2.36/1.10  prop_unsat_core_time:                   0.
% 2.36/1.10  
% 2.36/1.10  ------ QBF
% 2.36/1.10  
% 2.36/1.10  qbf_q_res:                              0
% 2.36/1.10  qbf_num_tautologies:                    0
% 2.36/1.10  qbf_prep_cycles:                        0
% 2.36/1.10  
% 2.36/1.10  ------ BMC1
% 2.36/1.10  
% 2.36/1.10  bmc1_current_bound:                     -1
% 2.36/1.10  bmc1_last_solved_bound:                 -1
% 2.36/1.10  bmc1_unsat_core_size:                   -1
% 2.36/1.10  bmc1_unsat_core_parents_size:           -1
% 2.36/1.10  bmc1_merge_next_fun:                    0
% 2.36/1.10  bmc1_unsat_core_clauses_time:           0.
% 2.36/1.10  
% 2.36/1.10  ------ Instantiation
% 2.36/1.10  
% 2.36/1.10  inst_num_of_clauses:                    801
% 2.36/1.10  inst_num_in_passive:                    113
% 2.36/1.10  inst_num_in_active:                     405
% 2.36/1.10  inst_num_in_unprocessed:                283
% 2.36/1.10  inst_num_of_loops:                      550
% 2.36/1.10  inst_num_of_learning_restarts:          0
% 2.36/1.10  inst_num_moves_active_passive:          141
% 2.36/1.10  inst_lit_activity:                      0
% 2.36/1.10  inst_lit_activity_moves:                0
% 2.36/1.10  inst_num_tautologies:                   0
% 2.36/1.10  inst_num_prop_implied:                  0
% 2.36/1.10  inst_num_existing_simplified:           0
% 2.36/1.10  inst_num_eq_res_simplified:             0
% 2.36/1.10  inst_num_child_elim:                    0
% 2.36/1.10  inst_num_of_dismatching_blockings:      226
% 2.36/1.10  inst_num_of_non_proper_insts:           698
% 2.36/1.10  inst_num_of_duplicates:                 0
% 2.36/1.10  inst_inst_num_from_inst_to_res:         0
% 2.36/1.10  inst_dismatching_checking_time:         0.
% 2.36/1.10  
% 2.36/1.10  ------ Resolution
% 2.36/1.10  
% 2.36/1.10  res_num_of_clauses:                     0
% 2.36/1.10  res_num_in_passive:                     0
% 2.36/1.10  res_num_in_active:                      0
% 2.36/1.10  res_num_of_loops:                       167
% 2.36/1.10  res_forward_subset_subsumed:            66
% 2.36/1.10  res_backward_subset_subsumed:           4
% 2.36/1.10  res_forward_subsumed:                   0
% 2.36/1.10  res_backward_subsumed:                  0
% 2.36/1.10  res_forward_subsumption_resolution:     4
% 2.36/1.10  res_backward_subsumption_resolution:    0
% 2.36/1.10  res_clause_to_clause_subsumption:       251
% 2.36/1.10  res_orphan_elimination:                 0
% 2.36/1.10  res_tautology_del:                      104
% 2.36/1.10  res_num_eq_res_simplified:              0
% 2.36/1.10  res_num_sel_changes:                    0
% 2.36/1.10  res_moves_from_active_to_pass:          0
% 2.36/1.10  
% 2.36/1.10  ------ Superposition
% 2.36/1.10  
% 2.36/1.10  sup_time_total:                         0.
% 2.36/1.10  sup_time_generating:                    0.
% 2.36/1.10  sup_time_sim_full:                      0.
% 2.36/1.10  sup_time_sim_immed:                     0.
% 2.36/1.10  
% 2.36/1.10  sup_num_of_clauses:                     115
% 2.36/1.10  sup_num_in_active:                      53
% 2.36/1.10  sup_num_in_passive:                     62
% 2.36/1.10  sup_num_of_loops:                       108
% 2.36/1.10  sup_fw_superposition:                   56
% 2.36/1.10  sup_bw_superposition:                   74
% 2.36/1.10  sup_immediate_simplified:               34
% 2.36/1.10  sup_given_eliminated:                   2
% 2.36/1.10  comparisons_done:                       0
% 2.36/1.10  comparisons_avoided:                    5
% 2.36/1.10  
% 2.36/1.10  ------ Simplifications
% 2.36/1.10  
% 2.36/1.10  
% 2.36/1.10  sim_fw_subset_subsumed:                 9
% 2.36/1.10  sim_bw_subset_subsumed:                 7
% 2.36/1.10  sim_fw_subsumed:                        7
% 2.36/1.10  sim_bw_subsumed:                        0
% 2.36/1.10  sim_fw_subsumption_res:                 2
% 2.36/1.10  sim_bw_subsumption_res:                 0
% 2.36/1.10  sim_tautology_del:                      4
% 2.36/1.10  sim_eq_tautology_del:                   12
% 2.36/1.10  sim_eq_res_simp:                        1
% 2.36/1.10  sim_fw_demodulated:                     13
% 2.36/1.10  sim_bw_demodulated:                     54
% 2.36/1.10  sim_light_normalised:                   40
% 2.36/1.10  sim_joinable_taut:                      0
% 2.36/1.10  sim_joinable_simp:                      0
% 2.36/1.10  sim_ac_normalised:                      0
% 2.36/1.10  sim_smt_subsumption:                    0
% 2.36/1.10  
%------------------------------------------------------------------------------
