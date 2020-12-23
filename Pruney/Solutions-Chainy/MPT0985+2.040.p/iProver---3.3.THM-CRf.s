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

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  183 (3906 expanded)
%              Number of clauses        :  117 (1172 expanded)
%              Number of leaves         :   16 ( 773 expanded)
%              Depth                    :   21
%              Number of atoms          :  588 (21410 expanded)
%              Number of equality atoms :  270 (3935 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(flattening,[],[f44])).

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
    inference(nnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

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
    inference(flattening,[],[f48])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).

fof(f90,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f64,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_622,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_624,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_36])).

cnf(c_1532,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1536,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4076,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1532,c_1536])).

cnf(c_4217,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_624,c_4076])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1535,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3220,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1532,c_1535])).

cnf(c_34,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3232,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3220,c_34])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1538,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2722,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1538])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1542,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2743,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2722,c_1542])).

cnf(c_3244,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3232,c_2743])).

cnf(c_4517,plain,
    ( k9_relat_1(sK2,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4217,c_3244])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1881,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1882,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_779,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_33])).

cnf(c_780,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_792,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_780,c_15])).

cnf(c_1513,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_781,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1862,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1863,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1862])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1865,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1866,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_2139,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_39,c_41,c_781,c_1863,c_1866,c_1882])).

cnf(c_2140,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2139])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_470,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_471,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_473,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_38])).

cnf(c_1527,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_1891,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1527,c_38,c_36,c_471,c_1881])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_438,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_439,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_441,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_38])).

cnf(c_1529,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_1895,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1529,c_38,c_36,c_439,c_1881])).

cnf(c_1897,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1895,c_1891])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_424,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_425,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_427,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_38])).

cnf(c_1530,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1910,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_38,c_36,c_425,c_1881])).

cnf(c_1912,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1910,c_1891])).

cnf(c_2143,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2140,c_1891,c_1897,c_1912])).

cnf(c_3245,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3232,c_2143])).

cnf(c_3249,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3245])).

cnf(c_4516,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4217,c_3249])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_744,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_21,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_379,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_21,c_19])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_21,c_19])).

cnf(c_384,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_383])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_384,c_26])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_548,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_0])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_548])).

cnf(c_751,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_744,c_549])).

cnf(c_1515,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1760,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1515,c_3])).

cnf(c_125,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_919,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1899,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_1900,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_1902,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1900])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_384,c_33])).

cnf(c_593,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_1522,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_594,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_2021,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1522,c_39,c_41,c_594,c_1863,c_1882])).

cnf(c_2316,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1760,c_125,c_1902,c_2021])).

cnf(c_2320,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2316,c_1891])).

cnf(c_4819,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4516,c_2320])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1533,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3690,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1533])).

cnf(c_3246,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3232,c_1912])).

cnf(c_3702,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3690,c_3246])).

cnf(c_4972,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4217,c_3702])).

cnf(c_1539,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5203,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_1539])).

cnf(c_1540,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5235,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1891,c_1540])).

cnf(c_5564,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4517,c_39,c_41,c_1882,c_2320,c_4516,c_4972,c_5203,c_5235])).

cnf(c_5570,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5564,c_3702])).

cnf(c_5659,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5570,c_3])).

cnf(c_5581,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5564,c_2320])).

cnf(c_5633,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5581])).

cnf(c_5635,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5633,c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5659,c_5635,c_5235,c_5203,c_1882,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:39:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.14/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.14/1.03  
% 1.14/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.14/1.03  
% 1.14/1.03  ------  iProver source info
% 1.14/1.03  
% 1.14/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.14/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.14/1.03  git: non_committed_changes: false
% 1.14/1.03  git: last_make_outside_of_git: false
% 1.14/1.03  
% 1.14/1.03  ------ 
% 1.14/1.03  
% 1.14/1.03  ------ Input Options
% 1.14/1.03  
% 1.14/1.03  --out_options                           all
% 1.14/1.03  --tptp_safe_out                         true
% 1.14/1.03  --problem_path                          ""
% 1.14/1.03  --include_path                          ""
% 1.14/1.03  --clausifier                            res/vclausify_rel
% 1.14/1.03  --clausifier_options                    --mode clausify
% 1.14/1.03  --stdin                                 false
% 1.14/1.03  --stats_out                             all
% 1.14/1.03  
% 1.14/1.03  ------ General Options
% 1.14/1.03  
% 1.14/1.03  --fof                                   false
% 1.14/1.03  --time_out_real                         305.
% 1.14/1.03  --time_out_virtual                      -1.
% 1.14/1.03  --symbol_type_check                     false
% 1.14/1.03  --clausify_out                          false
% 1.14/1.03  --sig_cnt_out                           false
% 1.14/1.03  --trig_cnt_out                          false
% 1.14/1.03  --trig_cnt_out_tolerance                1.
% 1.14/1.03  --trig_cnt_out_sk_spl                   false
% 1.14/1.03  --abstr_cl_out                          false
% 1.14/1.03  
% 1.14/1.03  ------ Global Options
% 1.14/1.03  
% 1.14/1.03  --schedule                              default
% 1.14/1.03  --add_important_lit                     false
% 1.14/1.03  --prop_solver_per_cl                    1000
% 1.14/1.03  --min_unsat_core                        false
% 1.14/1.03  --soft_assumptions                      false
% 1.14/1.03  --soft_lemma_size                       3
% 1.14/1.03  --prop_impl_unit_size                   0
% 1.14/1.03  --prop_impl_unit                        []
% 1.14/1.03  --share_sel_clauses                     true
% 1.14/1.03  --reset_solvers                         false
% 1.14/1.03  --bc_imp_inh                            [conj_cone]
% 1.14/1.03  --conj_cone_tolerance                   3.
% 1.14/1.03  --extra_neg_conj                        none
% 1.14/1.03  --large_theory_mode                     true
% 1.14/1.03  --prolific_symb_bound                   200
% 1.14/1.03  --lt_threshold                          2000
% 1.14/1.03  --clause_weak_htbl                      true
% 1.14/1.03  --gc_record_bc_elim                     false
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing Options
% 1.14/1.03  
% 1.14/1.03  --preprocessing_flag                    true
% 1.14/1.03  --time_out_prep_mult                    0.1
% 1.14/1.03  --splitting_mode                        input
% 1.14/1.03  --splitting_grd                         true
% 1.14/1.03  --splitting_cvd                         false
% 1.14/1.03  --splitting_cvd_svl                     false
% 1.14/1.03  --splitting_nvd                         32
% 1.14/1.03  --sub_typing                            true
% 1.14/1.03  --prep_gs_sim                           true
% 1.14/1.03  --prep_unflatten                        true
% 1.14/1.03  --prep_res_sim                          true
% 1.14/1.03  --prep_upred                            true
% 1.14/1.03  --prep_sem_filter                       exhaustive
% 1.14/1.03  --prep_sem_filter_out                   false
% 1.14/1.03  --pred_elim                             true
% 1.14/1.03  --res_sim_input                         true
% 1.14/1.03  --eq_ax_congr_red                       true
% 1.14/1.03  --pure_diseq_elim                       true
% 1.14/1.03  --brand_transform                       false
% 1.14/1.03  --non_eq_to_eq                          false
% 1.14/1.03  --prep_def_merge                        true
% 1.14/1.03  --prep_def_merge_prop_impl              false
% 1.14/1.03  --prep_def_merge_mbd                    true
% 1.14/1.03  --prep_def_merge_tr_red                 false
% 1.14/1.03  --prep_def_merge_tr_cl                  false
% 1.14/1.03  --smt_preprocessing                     true
% 1.14/1.03  --smt_ac_axioms                         fast
% 1.14/1.03  --preprocessed_out                      false
% 1.14/1.03  --preprocessed_stats                    false
% 1.14/1.03  
% 1.14/1.03  ------ Abstraction refinement Options
% 1.14/1.03  
% 1.14/1.03  --abstr_ref                             []
% 1.14/1.03  --abstr_ref_prep                        false
% 1.14/1.03  --abstr_ref_until_sat                   false
% 1.14/1.03  --abstr_ref_sig_restrict                funpre
% 1.14/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.14/1.03  --abstr_ref_under                       []
% 1.14/1.03  
% 1.14/1.03  ------ SAT Options
% 1.14/1.03  
% 1.14/1.03  --sat_mode                              false
% 1.14/1.03  --sat_fm_restart_options                ""
% 1.14/1.03  --sat_gr_def                            false
% 1.14/1.03  --sat_epr_types                         true
% 1.14/1.03  --sat_non_cyclic_types                  false
% 1.14/1.03  --sat_finite_models                     false
% 1.14/1.03  --sat_fm_lemmas                         false
% 1.14/1.03  --sat_fm_prep                           false
% 1.14/1.03  --sat_fm_uc_incr                        true
% 1.14/1.03  --sat_out_model                         small
% 1.14/1.03  --sat_out_clauses                       false
% 1.14/1.03  
% 1.14/1.03  ------ QBF Options
% 1.14/1.03  
% 1.14/1.03  --qbf_mode                              false
% 1.14/1.03  --qbf_elim_univ                         false
% 1.14/1.03  --qbf_dom_inst                          none
% 1.14/1.03  --qbf_dom_pre_inst                      false
% 1.14/1.03  --qbf_sk_in                             false
% 1.14/1.03  --qbf_pred_elim                         true
% 1.14/1.03  --qbf_split                             512
% 1.14/1.03  
% 1.14/1.03  ------ BMC1 Options
% 1.14/1.03  
% 1.14/1.03  --bmc1_incremental                      false
% 1.14/1.03  --bmc1_axioms                           reachable_all
% 1.14/1.03  --bmc1_min_bound                        0
% 1.14/1.03  --bmc1_max_bound                        -1
% 1.14/1.03  --bmc1_max_bound_default                -1
% 1.14/1.03  --bmc1_symbol_reachability              true
% 1.14/1.03  --bmc1_property_lemmas                  false
% 1.14/1.03  --bmc1_k_induction                      false
% 1.14/1.03  --bmc1_non_equiv_states                 false
% 1.14/1.03  --bmc1_deadlock                         false
% 1.14/1.03  --bmc1_ucm                              false
% 1.14/1.03  --bmc1_add_unsat_core                   none
% 1.14/1.03  --bmc1_unsat_core_children              false
% 1.14/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.14/1.03  --bmc1_out_stat                         full
% 1.14/1.03  --bmc1_ground_init                      false
% 1.14/1.03  --bmc1_pre_inst_next_state              false
% 1.14/1.03  --bmc1_pre_inst_state                   false
% 1.14/1.03  --bmc1_pre_inst_reach_state             false
% 1.14/1.03  --bmc1_out_unsat_core                   false
% 1.14/1.03  --bmc1_aig_witness_out                  false
% 1.14/1.03  --bmc1_verbose                          false
% 1.14/1.03  --bmc1_dump_clauses_tptp                false
% 1.14/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.14/1.03  --bmc1_dump_file                        -
% 1.14/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.14/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.14/1.03  --bmc1_ucm_extend_mode                  1
% 1.14/1.03  --bmc1_ucm_init_mode                    2
% 1.14/1.03  --bmc1_ucm_cone_mode                    none
% 1.14/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.14/1.03  --bmc1_ucm_relax_model                  4
% 1.14/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.14/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.14/1.03  --bmc1_ucm_layered_model                none
% 1.14/1.03  --bmc1_ucm_max_lemma_size               10
% 1.14/1.03  
% 1.14/1.03  ------ AIG Options
% 1.14/1.03  
% 1.14/1.03  --aig_mode                              false
% 1.14/1.03  
% 1.14/1.03  ------ Instantiation Options
% 1.14/1.03  
% 1.14/1.03  --instantiation_flag                    true
% 1.14/1.03  --inst_sos_flag                         false
% 1.14/1.03  --inst_sos_phase                        true
% 1.14/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel_side                     num_symb
% 1.14/1.03  --inst_solver_per_active                1400
% 1.14/1.03  --inst_solver_calls_frac                1.
% 1.14/1.03  --inst_passive_queue_type               priority_queues
% 1.14/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.14/1.03  --inst_passive_queues_freq              [25;2]
% 1.14/1.03  --inst_dismatching                      true
% 1.14/1.03  --inst_eager_unprocessed_to_passive     true
% 1.14/1.03  --inst_prop_sim_given                   true
% 1.14/1.03  --inst_prop_sim_new                     false
% 1.14/1.03  --inst_subs_new                         false
% 1.14/1.03  --inst_eq_res_simp                      false
% 1.14/1.03  --inst_subs_given                       false
% 1.14/1.03  --inst_orphan_elimination               true
% 1.14/1.03  --inst_learning_loop_flag               true
% 1.14/1.03  --inst_learning_start                   3000
% 1.14/1.03  --inst_learning_factor                  2
% 1.14/1.03  --inst_start_prop_sim_after_learn       3
% 1.14/1.03  --inst_sel_renew                        solver
% 1.14/1.03  --inst_lit_activity_flag                true
% 1.14/1.03  --inst_restr_to_given                   false
% 1.14/1.03  --inst_activity_threshold               500
% 1.14/1.03  --inst_out_proof                        true
% 1.14/1.03  
% 1.14/1.03  ------ Resolution Options
% 1.14/1.03  
% 1.14/1.03  --resolution_flag                       true
% 1.14/1.03  --res_lit_sel                           adaptive
% 1.14/1.03  --res_lit_sel_side                      none
% 1.14/1.03  --res_ordering                          kbo
% 1.14/1.03  --res_to_prop_solver                    active
% 1.14/1.03  --res_prop_simpl_new                    false
% 1.14/1.03  --res_prop_simpl_given                  true
% 1.14/1.03  --res_passive_queue_type                priority_queues
% 1.14/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.14/1.03  --res_passive_queues_freq               [15;5]
% 1.14/1.03  --res_forward_subs                      full
% 1.14/1.03  --res_backward_subs                     full
% 1.14/1.03  --res_forward_subs_resolution           true
% 1.14/1.03  --res_backward_subs_resolution          true
% 1.14/1.03  --res_orphan_elimination                true
% 1.14/1.03  --res_time_limit                        2.
% 1.14/1.03  --res_out_proof                         true
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Options
% 1.14/1.03  
% 1.14/1.03  --superposition_flag                    true
% 1.14/1.03  --sup_passive_queue_type                priority_queues
% 1.14/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.14/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.14/1.03  --demod_completeness_check              fast
% 1.14/1.03  --demod_use_ground                      true
% 1.14/1.03  --sup_to_prop_solver                    passive
% 1.14/1.03  --sup_prop_simpl_new                    true
% 1.14/1.03  --sup_prop_simpl_given                  true
% 1.14/1.03  --sup_fun_splitting                     false
% 1.14/1.03  --sup_smt_interval                      50000
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Simplification Setup
% 1.14/1.03  
% 1.14/1.03  --sup_indices_passive                   []
% 1.14/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.14/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_full_bw                           [BwDemod]
% 1.14/1.03  --sup_immed_triv                        [TrivRules]
% 1.14/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.14/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_immed_bw_main                     []
% 1.14/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.14/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  
% 1.14/1.03  ------ Combination Options
% 1.14/1.03  
% 1.14/1.03  --comb_res_mult                         3
% 1.14/1.03  --comb_sup_mult                         2
% 1.14/1.03  --comb_inst_mult                        10
% 1.14/1.03  
% 1.14/1.03  ------ Debug Options
% 1.14/1.03  
% 1.14/1.03  --dbg_backtrace                         false
% 1.14/1.03  --dbg_dump_prop_clauses                 false
% 1.14/1.03  --dbg_dump_prop_clauses_file            -
% 1.14/1.03  --dbg_out_stat                          false
% 1.14/1.03  ------ Parsing...
% 1.14/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.14/1.03  ------ Proving...
% 1.14/1.03  ------ Problem Properties 
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  clauses                                 41
% 1.14/1.03  conjectures                             3
% 1.14/1.03  EPR                                     3
% 1.14/1.03  Horn                                    32
% 1.14/1.03  unary                                   9
% 1.14/1.03  binary                                  10
% 1.14/1.03  lits                                    113
% 1.14/1.03  lits eq                                 48
% 1.14/1.03  fd_pure                                 0
% 1.14/1.03  fd_pseudo                               0
% 1.14/1.03  fd_cond                                 4
% 1.14/1.03  fd_pseudo_cond                          1
% 1.14/1.03  AC symbols                              0
% 1.14/1.03  
% 1.14/1.03  ------ Schedule dynamic 5 is on 
% 1.14/1.03  
% 1.14/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  ------ 
% 1.14/1.03  Current options:
% 1.14/1.03  ------ 
% 1.14/1.03  
% 1.14/1.03  ------ Input Options
% 1.14/1.03  
% 1.14/1.03  --out_options                           all
% 1.14/1.03  --tptp_safe_out                         true
% 1.14/1.03  --problem_path                          ""
% 1.14/1.03  --include_path                          ""
% 1.14/1.03  --clausifier                            res/vclausify_rel
% 1.14/1.03  --clausifier_options                    --mode clausify
% 1.14/1.03  --stdin                                 false
% 1.14/1.03  --stats_out                             all
% 1.14/1.03  
% 1.14/1.03  ------ General Options
% 1.14/1.03  
% 1.14/1.03  --fof                                   false
% 1.14/1.03  --time_out_real                         305.
% 1.14/1.03  --time_out_virtual                      -1.
% 1.14/1.03  --symbol_type_check                     false
% 1.14/1.03  --clausify_out                          false
% 1.14/1.03  --sig_cnt_out                           false
% 1.14/1.03  --trig_cnt_out                          false
% 1.14/1.03  --trig_cnt_out_tolerance                1.
% 1.14/1.03  --trig_cnt_out_sk_spl                   false
% 1.14/1.03  --abstr_cl_out                          false
% 1.14/1.03  
% 1.14/1.03  ------ Global Options
% 1.14/1.03  
% 1.14/1.03  --schedule                              default
% 1.14/1.03  --add_important_lit                     false
% 1.14/1.03  --prop_solver_per_cl                    1000
% 1.14/1.03  --min_unsat_core                        false
% 1.14/1.03  --soft_assumptions                      false
% 1.14/1.03  --soft_lemma_size                       3
% 1.14/1.03  --prop_impl_unit_size                   0
% 1.14/1.03  --prop_impl_unit                        []
% 1.14/1.03  --share_sel_clauses                     true
% 1.14/1.03  --reset_solvers                         false
% 1.14/1.03  --bc_imp_inh                            [conj_cone]
% 1.14/1.03  --conj_cone_tolerance                   3.
% 1.14/1.03  --extra_neg_conj                        none
% 1.14/1.03  --large_theory_mode                     true
% 1.14/1.03  --prolific_symb_bound                   200
% 1.14/1.03  --lt_threshold                          2000
% 1.14/1.03  --clause_weak_htbl                      true
% 1.14/1.03  --gc_record_bc_elim                     false
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing Options
% 1.14/1.03  
% 1.14/1.03  --preprocessing_flag                    true
% 1.14/1.03  --time_out_prep_mult                    0.1
% 1.14/1.03  --splitting_mode                        input
% 1.14/1.03  --splitting_grd                         true
% 1.14/1.03  --splitting_cvd                         false
% 1.14/1.03  --splitting_cvd_svl                     false
% 1.14/1.03  --splitting_nvd                         32
% 1.14/1.03  --sub_typing                            true
% 1.14/1.03  --prep_gs_sim                           true
% 1.14/1.03  --prep_unflatten                        true
% 1.14/1.03  --prep_res_sim                          true
% 1.14/1.03  --prep_upred                            true
% 1.14/1.03  --prep_sem_filter                       exhaustive
% 1.14/1.03  --prep_sem_filter_out                   false
% 1.14/1.03  --pred_elim                             true
% 1.14/1.03  --res_sim_input                         true
% 1.14/1.03  --eq_ax_congr_red                       true
% 1.14/1.03  --pure_diseq_elim                       true
% 1.14/1.03  --brand_transform                       false
% 1.14/1.03  --non_eq_to_eq                          false
% 1.14/1.03  --prep_def_merge                        true
% 1.14/1.03  --prep_def_merge_prop_impl              false
% 1.14/1.03  --prep_def_merge_mbd                    true
% 1.14/1.03  --prep_def_merge_tr_red                 false
% 1.14/1.03  --prep_def_merge_tr_cl                  false
% 1.14/1.03  --smt_preprocessing                     true
% 1.14/1.03  --smt_ac_axioms                         fast
% 1.14/1.03  --preprocessed_out                      false
% 1.14/1.03  --preprocessed_stats                    false
% 1.14/1.03  
% 1.14/1.03  ------ Abstraction refinement Options
% 1.14/1.03  
% 1.14/1.03  --abstr_ref                             []
% 1.14/1.03  --abstr_ref_prep                        false
% 1.14/1.03  --abstr_ref_until_sat                   false
% 1.14/1.03  --abstr_ref_sig_restrict                funpre
% 1.14/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.14/1.03  --abstr_ref_under                       []
% 1.14/1.03  
% 1.14/1.03  ------ SAT Options
% 1.14/1.03  
% 1.14/1.03  --sat_mode                              false
% 1.14/1.03  --sat_fm_restart_options                ""
% 1.14/1.03  --sat_gr_def                            false
% 1.14/1.03  --sat_epr_types                         true
% 1.14/1.03  --sat_non_cyclic_types                  false
% 1.14/1.03  --sat_finite_models                     false
% 1.14/1.03  --sat_fm_lemmas                         false
% 1.14/1.03  --sat_fm_prep                           false
% 1.14/1.03  --sat_fm_uc_incr                        true
% 1.14/1.03  --sat_out_model                         small
% 1.14/1.03  --sat_out_clauses                       false
% 1.14/1.03  
% 1.14/1.03  ------ QBF Options
% 1.14/1.03  
% 1.14/1.03  --qbf_mode                              false
% 1.14/1.03  --qbf_elim_univ                         false
% 1.14/1.03  --qbf_dom_inst                          none
% 1.14/1.03  --qbf_dom_pre_inst                      false
% 1.14/1.03  --qbf_sk_in                             false
% 1.14/1.03  --qbf_pred_elim                         true
% 1.14/1.03  --qbf_split                             512
% 1.14/1.03  
% 1.14/1.03  ------ BMC1 Options
% 1.14/1.03  
% 1.14/1.03  --bmc1_incremental                      false
% 1.14/1.03  --bmc1_axioms                           reachable_all
% 1.14/1.03  --bmc1_min_bound                        0
% 1.14/1.03  --bmc1_max_bound                        -1
% 1.14/1.03  --bmc1_max_bound_default                -1
% 1.14/1.03  --bmc1_symbol_reachability              true
% 1.14/1.03  --bmc1_property_lemmas                  false
% 1.14/1.03  --bmc1_k_induction                      false
% 1.14/1.03  --bmc1_non_equiv_states                 false
% 1.14/1.03  --bmc1_deadlock                         false
% 1.14/1.03  --bmc1_ucm                              false
% 1.14/1.03  --bmc1_add_unsat_core                   none
% 1.14/1.03  --bmc1_unsat_core_children              false
% 1.14/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.14/1.03  --bmc1_out_stat                         full
% 1.14/1.03  --bmc1_ground_init                      false
% 1.14/1.03  --bmc1_pre_inst_next_state              false
% 1.14/1.03  --bmc1_pre_inst_state                   false
% 1.14/1.03  --bmc1_pre_inst_reach_state             false
% 1.14/1.03  --bmc1_out_unsat_core                   false
% 1.14/1.03  --bmc1_aig_witness_out                  false
% 1.14/1.03  --bmc1_verbose                          false
% 1.14/1.03  --bmc1_dump_clauses_tptp                false
% 1.14/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.14/1.03  --bmc1_dump_file                        -
% 1.14/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.14/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.14/1.03  --bmc1_ucm_extend_mode                  1
% 1.14/1.03  --bmc1_ucm_init_mode                    2
% 1.14/1.03  --bmc1_ucm_cone_mode                    none
% 1.14/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.14/1.03  --bmc1_ucm_relax_model                  4
% 1.14/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.14/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.14/1.03  --bmc1_ucm_layered_model                none
% 1.14/1.03  --bmc1_ucm_max_lemma_size               10
% 1.14/1.03  
% 1.14/1.03  ------ AIG Options
% 1.14/1.03  
% 1.14/1.03  --aig_mode                              false
% 1.14/1.03  
% 1.14/1.03  ------ Instantiation Options
% 1.14/1.03  
% 1.14/1.03  --instantiation_flag                    true
% 1.14/1.03  --inst_sos_flag                         false
% 1.14/1.03  --inst_sos_phase                        true
% 1.14/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel_side                     none
% 1.14/1.03  --inst_solver_per_active                1400
% 1.14/1.03  --inst_solver_calls_frac                1.
% 1.14/1.03  --inst_passive_queue_type               priority_queues
% 1.14/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.14/1.03  --inst_passive_queues_freq              [25;2]
% 1.14/1.03  --inst_dismatching                      true
% 1.14/1.03  --inst_eager_unprocessed_to_passive     true
% 1.14/1.03  --inst_prop_sim_given                   true
% 1.14/1.03  --inst_prop_sim_new                     false
% 1.14/1.03  --inst_subs_new                         false
% 1.14/1.03  --inst_eq_res_simp                      false
% 1.14/1.03  --inst_subs_given                       false
% 1.14/1.03  --inst_orphan_elimination               true
% 1.14/1.03  --inst_learning_loop_flag               true
% 1.14/1.03  --inst_learning_start                   3000
% 1.14/1.03  --inst_learning_factor                  2
% 1.14/1.03  --inst_start_prop_sim_after_learn       3
% 1.14/1.03  --inst_sel_renew                        solver
% 1.14/1.03  --inst_lit_activity_flag                true
% 1.14/1.03  --inst_restr_to_given                   false
% 1.14/1.03  --inst_activity_threshold               500
% 1.14/1.03  --inst_out_proof                        true
% 1.14/1.03  
% 1.14/1.03  ------ Resolution Options
% 1.14/1.03  
% 1.14/1.03  --resolution_flag                       false
% 1.14/1.03  --res_lit_sel                           adaptive
% 1.14/1.03  --res_lit_sel_side                      none
% 1.14/1.03  --res_ordering                          kbo
% 1.14/1.03  --res_to_prop_solver                    active
% 1.14/1.03  --res_prop_simpl_new                    false
% 1.14/1.03  --res_prop_simpl_given                  true
% 1.14/1.03  --res_passive_queue_type                priority_queues
% 1.14/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.14/1.03  --res_passive_queues_freq               [15;5]
% 1.14/1.03  --res_forward_subs                      full
% 1.14/1.03  --res_backward_subs                     full
% 1.14/1.03  --res_forward_subs_resolution           true
% 1.14/1.03  --res_backward_subs_resolution          true
% 1.14/1.03  --res_orphan_elimination                true
% 1.14/1.03  --res_time_limit                        2.
% 1.14/1.03  --res_out_proof                         true
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Options
% 1.14/1.03  
% 1.14/1.03  --superposition_flag                    true
% 1.14/1.03  --sup_passive_queue_type                priority_queues
% 1.14/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.14/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.14/1.03  --demod_completeness_check              fast
% 1.14/1.03  --demod_use_ground                      true
% 1.14/1.03  --sup_to_prop_solver                    passive
% 1.14/1.03  --sup_prop_simpl_new                    true
% 1.14/1.03  --sup_prop_simpl_given                  true
% 1.14/1.03  --sup_fun_splitting                     false
% 1.14/1.03  --sup_smt_interval                      50000
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Simplification Setup
% 1.14/1.03  
% 1.14/1.03  --sup_indices_passive                   []
% 1.14/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.14/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_full_bw                           [BwDemod]
% 1.14/1.03  --sup_immed_triv                        [TrivRules]
% 1.14/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.14/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_immed_bw_main                     []
% 1.14/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.14/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  
% 1.14/1.03  ------ Combination Options
% 1.14/1.03  
% 1.14/1.03  --comb_res_mult                         3
% 1.14/1.03  --comb_sup_mult                         2
% 1.14/1.03  --comb_inst_mult                        10
% 1.14/1.03  
% 1.14/1.03  ------ Debug Options
% 1.14/1.03  
% 1.14/1.03  --dbg_backtrace                         false
% 1.14/1.03  --dbg_dump_prop_clauses                 false
% 1.14/1.03  --dbg_dump_prop_clauses_file            -
% 1.14/1.03  --dbg_out_stat                          false
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  ------ Proving...
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  % SZS status Theorem for theBenchmark.p
% 1.14/1.03  
% 1.14/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.14/1.03  
% 1.14/1.03  fof(f19,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f44,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f19])).
% 1.14/1.03  
% 1.14/1.03  fof(f45,plain,(
% 1.14/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(flattening,[],[f44])).
% 1.14/1.03  
% 1.14/1.03  fof(f52,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(nnf_transformation,[],[f45])).
% 1.14/1.03  
% 1.14/1.03  fof(f77,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f52])).
% 1.14/1.03  
% 1.14/1.03  fof(f23,conjecture,(
% 1.14/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f24,negated_conjecture,(
% 1.14/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.14/1.03    inference(negated_conjecture,[],[f23])).
% 1.14/1.03  
% 1.14/1.03  fof(f48,plain,(
% 1.14/1.03    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.14/1.03    inference(ennf_transformation,[],[f24])).
% 1.14/1.03  
% 1.14/1.03  fof(f49,plain,(
% 1.14/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.14/1.03    inference(flattening,[],[f48])).
% 1.14/1.03  
% 1.14/1.03  fof(f53,plain,(
% 1.14/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.14/1.03    introduced(choice_axiom,[])).
% 1.14/1.03  
% 1.14/1.03  fof(f54,plain,(
% 1.14/1.03    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.14/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).
% 1.14/1.03  
% 1.14/1.03  fof(f90,plain,(
% 1.14/1.03    v1_funct_2(sK2,sK0,sK1)),
% 1.14/1.03    inference(cnf_transformation,[],[f54])).
% 1.14/1.03  
% 1.14/1.03  fof(f91,plain,(
% 1.14/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.14/1.03    inference(cnf_transformation,[],[f54])).
% 1.14/1.03  
% 1.14/1.03  fof(f15,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f39,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f15])).
% 1.14/1.03  
% 1.14/1.03  fof(f72,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f39])).
% 1.14/1.03  
% 1.14/1.03  fof(f16,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f40,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f16])).
% 1.14/1.03  
% 1.14/1.03  fof(f73,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f40])).
% 1.14/1.03  
% 1.14/1.03  fof(f93,plain,(
% 1.14/1.03    k2_relset_1(sK0,sK1,sK2) = sK1),
% 1.14/1.03    inference(cnf_transformation,[],[f54])).
% 1.14/1.03  
% 1.14/1.03  fof(f13,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f37,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f13])).
% 1.14/1.03  
% 1.14/1.03  fof(f70,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f37])).
% 1.14/1.03  
% 1.14/1.03  fof(f6,axiom,(
% 1.14/1.03    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f27,plain,(
% 1.14/1.03    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(ennf_transformation,[],[f6])).
% 1.14/1.03  
% 1.14/1.03  fof(f61,plain,(
% 1.14/1.03    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f27])).
% 1.14/1.03  
% 1.14/1.03  fof(f89,plain,(
% 1.14/1.03    v1_funct_1(sK2)),
% 1.14/1.03    inference(cnf_transformation,[],[f54])).
% 1.14/1.03  
% 1.14/1.03  fof(f22,axiom,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f46,plain,(
% 1.14/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.14/1.03    inference(ennf_transformation,[],[f22])).
% 1.14/1.03  
% 1.14/1.03  fof(f47,plain,(
% 1.14/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(flattening,[],[f46])).
% 1.14/1.03  
% 1.14/1.03  fof(f87,plain,(
% 1.14/1.03    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f47])).
% 1.14/1.03  
% 1.14/1.03  fof(f94,plain,(
% 1.14/1.03    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.14/1.03    inference(cnf_transformation,[],[f54])).
% 1.14/1.03  
% 1.14/1.03  fof(f10,axiom,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f31,plain,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.14/1.03    inference(ennf_transformation,[],[f10])).
% 1.14/1.03  
% 1.14/1.03  fof(f32,plain,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(flattening,[],[f31])).
% 1.14/1.03  
% 1.14/1.03  fof(f66,plain,(
% 1.14/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f32])).
% 1.14/1.03  
% 1.14/1.03  fof(f65,plain,(
% 1.14/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f32])).
% 1.14/1.03  
% 1.14/1.03  fof(f9,axiom,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f29,plain,(
% 1.14/1.03    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.14/1.03    inference(ennf_transformation,[],[f9])).
% 1.14/1.03  
% 1.14/1.03  fof(f30,plain,(
% 1.14/1.03    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(flattening,[],[f29])).
% 1.14/1.03  
% 1.14/1.03  fof(f64,plain,(
% 1.14/1.03    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f30])).
% 1.14/1.03  
% 1.14/1.03  fof(f92,plain,(
% 1.14/1.03    v2_funct_1(sK2)),
% 1.14/1.03    inference(cnf_transformation,[],[f54])).
% 1.14/1.03  
% 1.14/1.03  fof(f12,axiom,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f35,plain,(
% 1.14/1.03    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.14/1.03    inference(ennf_transformation,[],[f12])).
% 1.14/1.03  
% 1.14/1.03  fof(f36,plain,(
% 1.14/1.03    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(flattening,[],[f35])).
% 1.14/1.03  
% 1.14/1.03  fof(f69,plain,(
% 1.14/1.03    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f36])).
% 1.14/1.03  
% 1.14/1.03  fof(f68,plain,(
% 1.14/1.03    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f36])).
% 1.14/1.03  
% 1.14/1.03  fof(f80,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f52])).
% 1.14/1.03  
% 1.14/1.03  fof(f101,plain,(
% 1.14/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.14/1.03    inference(equality_resolution,[],[f80])).
% 1.14/1.03  
% 1.14/1.03  fof(f18,axiom,(
% 1.14/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f43,plain,(
% 1.14/1.03    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.14/1.03    inference(ennf_transformation,[],[f18])).
% 1.14/1.03  
% 1.14/1.03  fof(f76,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f43])).
% 1.14/1.03  
% 1.14/1.03  fof(f17,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f41,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f17])).
% 1.14/1.03  
% 1.14/1.03  fof(f42,plain,(
% 1.14/1.03    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(flattening,[],[f41])).
% 1.14/1.03  
% 1.14/1.03  fof(f75,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f42])).
% 1.14/1.03  
% 1.14/1.03  fof(f78,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f52])).
% 1.14/1.03  
% 1.14/1.03  fof(f102,plain,(
% 1.14/1.03    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.14/1.03    inference(equality_resolution,[],[f78])).
% 1.14/1.03  
% 1.14/1.03  fof(f1,axiom,(
% 1.14/1.03    v1_xboole_0(k1_xboole_0)),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f55,plain,(
% 1.14/1.03    v1_xboole_0(k1_xboole_0)),
% 1.14/1.03    inference(cnf_transformation,[],[f1])).
% 1.14/1.03  
% 1.14/1.03  fof(f3,axiom,(
% 1.14/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.14/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f50,plain,(
% 1.14/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.14/1.03    inference(nnf_transformation,[],[f3])).
% 1.14/1.03  
% 1.14/1.03  fof(f51,plain,(
% 1.14/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.14/1.03    inference(flattening,[],[f50])).
% 1.14/1.03  
% 1.14/1.03  fof(f58,plain,(
% 1.14/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.14/1.03    inference(cnf_transformation,[],[f51])).
% 1.14/1.03  
% 1.14/1.03  fof(f97,plain,(
% 1.14/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.14/1.03    inference(equality_resolution,[],[f58])).
% 1.14/1.03  
% 1.14/1.03  fof(f88,plain,(
% 1.14/1.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f47])).
% 1.14/1.03  
% 1.14/1.03  cnf(c_27,plain,
% 1.14/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | k1_relset_1(X1,X2,X0) = X1
% 1.14/1.03      | k1_xboole_0 = X2 ),
% 1.14/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_37,negated_conjecture,
% 1.14/1.03      ( v1_funct_2(sK2,sK0,sK1) ),
% 1.14/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_621,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | k1_relset_1(X1,X2,X0) = X1
% 1.14/1.03      | sK0 != X1
% 1.14/1.03      | sK1 != X2
% 1.14/1.03      | sK2 != X0
% 1.14/1.03      | k1_xboole_0 = X2 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_622,plain,
% 1.14/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.14/1.03      | k1_relset_1(sK0,sK1,sK2) = sK0
% 1.14/1.03      | k1_xboole_0 = sK1 ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_621]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_36,negated_conjecture,
% 1.14/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.14/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_624,plain,
% 1.14/1.03      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_622,c_36]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1532,plain,
% 1.14/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_17,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1536,plain,
% 1.14/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.14/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_4076,plain,
% 1.14/1.03      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1532,c_1536]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_4217,plain,
% 1.14/1.03      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_624,c_4076]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_18,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1535,plain,
% 1.14/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.14/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3220,plain,
% 1.14/1.03      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1532,c_1535]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_34,negated_conjecture,
% 1.14/1.03      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 1.14/1.03      inference(cnf_transformation,[],[f93]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3232,plain,
% 1.14/1.03      ( k2_relat_1(sK2) = sK1 ),
% 1.14/1.03      inference(light_normalisation,[status(thm)],[c_3220,c_34]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_15,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | v1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1538,plain,
% 1.14/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.14/1.03      | v1_relat_1(X0) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2722,plain,
% 1.14/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1532,c_1538]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_6,plain,
% 1.14/1.03      ( ~ v1_relat_1(X0)
% 1.14/1.03      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1542,plain,
% 1.14/1.03      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 1.14/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2743,plain,
% 1.14/1.03      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_2722,c_1542]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3244,plain,
% 1.14/1.03      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_3232,c_2743]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_4517,plain,
% 1.14/1.03      ( k9_relat_1(sK2,sK0) = sK1 | sK1 = k1_xboole_0 ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_4217,c_3244]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_38,negated_conjecture,
% 1.14/1.03      ( v1_funct_1(sK2) ),
% 1.14/1.03      inference(cnf_transformation,[],[f89]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_39,plain,
% 1.14/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_41,plain,
% 1.14/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1881,plain,
% 1.14/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.14/1.03      | v1_relat_1(sK2) ),
% 1.14/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1882,plain,
% 1.14/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 1.14/1.03      | v1_relat_1(sK2) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_31,plain,
% 1.14/1.03      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f87]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_33,negated_conjecture,
% 1.14/1.03      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 1.14/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 1.14/1.03      inference(cnf_transformation,[],[f94]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_779,plain,
% 1.14/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k2_funct_1(sK2) != X0
% 1.14/1.03      | k2_relat_1(X0) != sK0
% 1.14/1.03      | k1_relat_1(X0) != sK1 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_31,c_33]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_780,plain,
% 1.14/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | ~ v1_relat_1(k2_funct_1(sK2))
% 1.14/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_779]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_792,plain,
% 1.14/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.14/1.03      inference(forward_subsumption_resolution,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_780,c_15]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1513,plain,
% 1.14/1.03      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_781,plain,
% 1.14/1.03      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_10,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | v1_funct_1(k2_funct_1(X0))
% 1.14/1.03      | ~ v1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1862,plain,
% 1.14/1.03      ( v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | ~ v1_funct_1(sK2)
% 1.14/1.03      | ~ v1_relat_1(sK2) ),
% 1.14/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1863,plain,
% 1.14/1.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.14/1.03      | v1_funct_1(sK2) != iProver_top
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_1862]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_11,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | v1_relat_1(k2_funct_1(X0)) ),
% 1.14/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1865,plain,
% 1.14/1.03      ( ~ v1_funct_1(sK2)
% 1.14/1.03      | v1_relat_1(k2_funct_1(sK2))
% 1.14/1.03      | ~ v1_relat_1(sK2) ),
% 1.14/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1866,plain,
% 1.14/1.03      ( v1_funct_1(sK2) != iProver_top
% 1.14/1.03      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2139,plain,
% 1.14/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1513,c_39,c_41,c_781,c_1863,c_1866,c_1882]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2140,plain,
% 1.14/1.03      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(renaming,[status(thm)],[c_2139]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_9,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v2_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_35,negated_conjecture,
% 1.14/1.03      ( v2_funct_1(sK2) ),
% 1.14/1.03      inference(cnf_transformation,[],[f92]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_470,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k2_funct_1(X0) = k4_relat_1(X0)
% 1.14/1.03      | sK2 != X0 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_35]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_471,plain,
% 1.14/1.03      ( ~ v1_funct_1(sK2)
% 1.14/1.03      | ~ v1_relat_1(sK2)
% 1.14/1.03      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_470]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_473,plain,
% 1.14/1.03      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_471,c_38]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1527,plain,
% 1.14/1.03      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1891,plain,
% 1.14/1.03      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1527,c_38,c_36,c_471,c_1881]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_13,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v2_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_438,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.14/1.03      | sK2 != X0 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_439,plain,
% 1.14/1.03      ( ~ v1_funct_1(sK2)
% 1.14/1.03      | ~ v1_relat_1(sK2)
% 1.14/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_438]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_441,plain,
% 1.14/1.03      ( ~ v1_relat_1(sK2)
% 1.14/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_439,c_38]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1529,plain,
% 1.14/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1895,plain,
% 1.14/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1529,c_38,c_36,c_439,c_1881]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1897,plain,
% 1.14/1.03      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(light_normalisation,[status(thm)],[c_1895,c_1891]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_14,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v2_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_424,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 1.14/1.03      | sK2 != X0 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_425,plain,
% 1.14/1.03      ( ~ v1_funct_1(sK2)
% 1.14/1.03      | ~ v1_relat_1(sK2)
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_424]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_427,plain,
% 1.14/1.03      ( ~ v1_relat_1(sK2)
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_425,c_38]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1530,plain,
% 1.14/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1910,plain,
% 1.14/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1530,c_38,c_36,c_425,c_1881]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1912,plain,
% 1.14/1.03      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(light_normalisation,[status(thm)],[c_1910,c_1891]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2143,plain,
% 1.14/1.03      ( k2_relat_1(sK2) != sK1
% 1.14/1.03      | k1_relat_1(sK2) != sK0
% 1.14/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(light_normalisation,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_2140,c_1891,c_1897,c_1912]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3245,plain,
% 1.14/1.03      ( k1_relat_1(sK2) != sK0
% 1.14/1.03      | sK1 != sK1
% 1.14/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_3232,c_2143]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3249,plain,
% 1.14/1.03      ( k1_relat_1(sK2) != sK0
% 1.14/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(equality_resolution_simp,[status(thm)],[c_3245]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_4516,plain,
% 1.14/1.03      ( sK1 = k1_xboole_0
% 1.14/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_4217,c_3249]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_24,plain,
% 1.14/1.03      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.14/1.03      inference(cnf_transformation,[],[f101]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_743,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.14/1.03      | k2_funct_1(sK2) != X0
% 1.14/1.03      | sK0 != X1
% 1.14/1.03      | sK1 != k1_xboole_0 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_744,plain,
% 1.14/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.03      | sK1 != k1_xboole_0 ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_743]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_21,plain,
% 1.14/1.03      ( v1_partfun1(X0,X1)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | ~ v1_xboole_0(X1) ),
% 1.14/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_19,plain,
% 1.14/1.03      ( v1_funct_2(X0,X1,X2)
% 1.14/1.03      | ~ v1_partfun1(X0,X1)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | ~ v1_funct_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_379,plain,
% 1.14/1.03      ( v1_funct_2(X0,X1,X2)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_xboole_0(X1) ),
% 1.14/1.03      inference(resolution,[status(thm)],[c_21,c_19]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_383,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | v1_funct_2(X0,X1,X2)
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_xboole_0(X1) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_379,c_21,c_19]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_384,plain,
% 1.14/1.03      ( v1_funct_2(X0,X1,X2)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_xboole_0(X1) ),
% 1.14/1.03      inference(renaming,[status(thm)],[c_383]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_26,plain,
% 1.14/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.14/1.03      inference(cnf_transformation,[],[f102]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_543,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_xboole_0(X1)
% 1.14/1.03      | X3 != X0
% 1.14/1.03      | X4 != X2
% 1.14/1.03      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 1.14/1.03      | k1_xboole_0 != X1 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_384,c_26]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_544,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_xboole_0(k1_xboole_0)
% 1.14/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_543]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_0,plain,
% 1.14/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_548,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_544,c_0]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_549,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.14/1.03      inference(renaming,[status(thm)],[c_548]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_751,plain,
% 1.14/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | sK1 != k1_xboole_0 ),
% 1.14/1.03      inference(forward_subsumption_resolution,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_744,c_549]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1515,plain,
% 1.14/1.03      ( sK1 != k1_xboole_0
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3,plain,
% 1.14/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.14/1.03      inference(cnf_transformation,[],[f97]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1760,plain,
% 1.14/1.03      ( sK1 != k1_xboole_0
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_1515,c_3]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_125,plain,
% 1.14/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_919,plain,
% 1.14/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.14/1.03      theory(equality) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1899,plain,
% 1.14/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 1.14/1.03      inference(instantiation,[status(thm)],[c_919]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1900,plain,
% 1.14/1.03      ( sK1 != X0
% 1.14/1.03      | v1_xboole_0(X0) != iProver_top
% 1.14/1.03      | v1_xboole_0(sK1) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1902,plain,
% 1.14/1.03      ( sK1 != k1_xboole_0
% 1.14/1.03      | v1_xboole_0(sK1) = iProver_top
% 1.14/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.14/1.03      inference(instantiation,[status(thm)],[c_1900]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_592,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | ~ v1_xboole_0(X1)
% 1.14/1.03      | k2_funct_1(sK2) != X0
% 1.14/1.03      | sK0 != X2
% 1.14/1.03      | sK1 != X1 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_384,c_33]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_593,plain,
% 1.14/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.03      | ~ v1_xboole_0(sK1) ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_592]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1522,plain,
% 1.14/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.03      | v1_xboole_0(sK1) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_594,plain,
% 1.14/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.03      | v1_xboole_0(sK1) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2021,plain,
% 1.14/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.03      | v1_xboole_0(sK1) != iProver_top ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1522,c_39,c_41,c_594,c_1863,c_1882]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2316,plain,
% 1.14/1.03      ( sK1 != k1_xboole_0
% 1.14/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1760,c_125,c_1902,c_2021]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_2320,plain,
% 1.14/1.03      ( sK1 != k1_xboole_0
% 1.14/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(light_normalisation,[status(thm)],[c_2316,c_1891]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_4819,plain,
% 1.14/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_4516,c_2320]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_30,plain,
% 1.14/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f88]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1533,plain,
% 1.14/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 1.14/1.03      | v1_funct_1(X0) != iProver_top
% 1.14/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3690,plain,
% 1.14/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 1.14/1.03      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 1.14/1.03      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1897,c_1533]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3246,plain,
% 1.14/1.03      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_3232,c_1912]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3702,plain,
% 1.14/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 1.14/1.03      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 1.14/1.03      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(light_normalisation,[status(thm)],[c_3690,c_3246]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_4972,plain,
% 1.14/1.03      ( sK1 = k1_xboole_0
% 1.14/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 1.14/1.03      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 1.14/1.03      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_4217,c_3702]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1539,plain,
% 1.14/1.03      ( v1_funct_1(X0) != iProver_top
% 1.14/1.03      | v1_relat_1(X0) != iProver_top
% 1.14/1.03      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5203,plain,
% 1.14/1.03      ( v1_funct_1(sK2) != iProver_top
% 1.14/1.03      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1891,c_1539]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1540,plain,
% 1.14/1.03      ( v1_funct_1(X0) != iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 1.14/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5235,plain,
% 1.14/1.03      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 1.14/1.03      | v1_funct_1(sK2) != iProver_top
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1891,c_1540]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5564,plain,
% 1.14/1.03      ( sK1 = k1_xboole_0 ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_4517,c_39,c_41,c_1882,c_2320,c_4516,c_4972,c_5203,
% 1.14/1.03                 c_5235]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5570,plain,
% 1.14/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
% 1.14/1.03      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 1.14/1.03      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_5564,c_3702]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5659,plain,
% 1.14/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.14/1.03      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 1.14/1.03      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_5570,c_3]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5581,plain,
% 1.14/1.03      ( k1_xboole_0 != k1_xboole_0
% 1.14/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_5564,c_2320]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5633,plain,
% 1.14/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.14/1.03      inference(equality_resolution_simp,[status(thm)],[c_5581]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_5635,plain,
% 1.14/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_5633,c_3]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(contradiction,plain,
% 1.14/1.03      ( $false ),
% 1.14/1.03      inference(minisat,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_5659,c_5635,c_5235,c_5203,c_1882,c_41,c_39]) ).
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.14/1.03  
% 1.14/1.03  ------                               Statistics
% 1.14/1.03  
% 1.14/1.03  ------ General
% 1.14/1.03  
% 1.14/1.03  abstr_ref_over_cycles:                  0
% 1.14/1.03  abstr_ref_under_cycles:                 0
% 1.14/1.03  gc_basic_clause_elim:                   0
% 1.14/1.03  forced_gc_time:                         0
% 1.14/1.03  parsing_time:                           0.011
% 1.14/1.03  unif_index_cands_time:                  0.
% 1.14/1.03  unif_index_add_time:                    0.
% 1.14/1.03  orderings_time:                         0.
% 1.14/1.03  out_proof_time:                         0.011
% 1.14/1.03  total_time:                             0.191
% 1.14/1.03  num_of_symbols:                         53
% 1.14/1.03  num_of_terms:                           4786
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing
% 1.14/1.03  
% 1.14/1.03  num_of_splits:                          0
% 1.14/1.03  num_of_split_atoms:                     0
% 1.14/1.03  num_of_reused_defs:                     0
% 1.14/1.03  num_eq_ax_congr_red:                    5
% 1.14/1.03  num_of_sem_filtered_clauses:            1
% 1.14/1.03  num_of_subtypes:                        0
% 1.14/1.03  monotx_restored_types:                  0
% 1.14/1.03  sat_num_of_epr_types:                   0
% 1.14/1.03  sat_num_of_non_cyclic_types:            0
% 1.14/1.03  sat_guarded_non_collapsed_types:        0
% 1.14/1.03  num_pure_diseq_elim:                    0
% 1.14/1.03  simp_replaced_by:                       0
% 1.14/1.03  res_preprocessed:                       154
% 1.14/1.03  prep_upred:                             0
% 1.14/1.03  prep_unflattend:                        67
% 1.14/1.03  smt_new_axioms:                         0
% 1.14/1.03  pred_elim_cands:                        7
% 1.14/1.03  pred_elim:                              3
% 1.14/1.03  pred_elim_cl:                           -4
% 1.14/1.03  pred_elim_cycles:                       4
% 1.14/1.03  merged_defs:                            0
% 1.14/1.03  merged_defs_ncl:                        0
% 1.14/1.03  bin_hyper_res:                          0
% 1.14/1.03  prep_cycles:                            3
% 1.14/1.03  pred_elim_time:                         0.009
% 1.14/1.03  splitting_time:                         0.
% 1.14/1.03  sem_filter_time:                        0.
% 1.14/1.03  monotx_time:                            0.
% 1.14/1.03  subtype_inf_time:                       0.
% 1.14/1.03  
% 1.14/1.03  ------ Problem properties
% 1.14/1.03  
% 1.14/1.03  clauses:                                41
% 1.14/1.03  conjectures:                            3
% 1.14/1.03  epr:                                    3
% 1.14/1.03  horn:                                   32
% 1.14/1.03  ground:                                 17
% 1.14/1.03  unary:                                  9
% 1.14/1.03  binary:                                 10
% 1.14/1.03  lits:                                   113
% 1.14/1.03  lits_eq:                                48
% 1.14/1.03  fd_pure:                                0
% 1.14/1.03  fd_pseudo:                              0
% 1.14/1.03  fd_cond:                                4
% 1.14/1.03  fd_pseudo_cond:                         1
% 1.14/1.03  ac_symbols:                             0
% 1.14/1.03  
% 1.14/1.03  ------ Propositional Solver
% 1.14/1.03  
% 1.14/1.03  prop_solver_calls:                      23
% 1.14/1.03  prop_fast_solver_calls:                 1150
% 1.14/1.03  smt_solver_calls:                       0
% 1.14/1.03  smt_fast_solver_calls:                  0
% 1.14/1.03  prop_num_of_clauses:                    2012
% 1.14/1.03  prop_preprocess_simplified:             6670
% 1.14/1.03  prop_fo_subsumed:                       31
% 1.14/1.03  prop_solver_time:                       0.
% 1.14/1.03  smt_solver_time:                        0.
% 1.14/1.03  smt_fast_solver_time:                   0.
% 1.14/1.03  prop_fast_solver_time:                  0.
% 1.14/1.03  prop_unsat_core_time:                   0.
% 1.14/1.03  
% 1.14/1.03  ------ QBF
% 1.14/1.03  
% 1.14/1.03  qbf_q_res:                              0
% 1.14/1.03  qbf_num_tautologies:                    0
% 1.14/1.03  qbf_prep_cycles:                        0
% 1.14/1.03  
% 1.14/1.03  ------ BMC1
% 1.14/1.03  
% 1.14/1.03  bmc1_current_bound:                     -1
% 1.14/1.03  bmc1_last_solved_bound:                 -1
% 1.14/1.03  bmc1_unsat_core_size:                   -1
% 1.14/1.03  bmc1_unsat_core_parents_size:           -1
% 1.14/1.03  bmc1_merge_next_fun:                    0
% 1.14/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.14/1.03  
% 1.14/1.03  ------ Instantiation
% 1.14/1.03  
% 1.14/1.03  inst_num_of_clauses:                    710
% 1.14/1.03  inst_num_in_passive:                    181
% 1.14/1.03  inst_num_in_active:                     328
% 1.14/1.03  inst_num_in_unprocessed:                201
% 1.14/1.03  inst_num_of_loops:                      350
% 1.14/1.03  inst_num_of_learning_restarts:          0
% 1.14/1.03  inst_num_moves_active_passive:          20
% 1.14/1.03  inst_lit_activity:                      0
% 1.14/1.03  inst_lit_activity_moves:                0
% 1.14/1.03  inst_num_tautologies:                   0
% 1.14/1.03  inst_num_prop_implied:                  0
% 1.14/1.03  inst_num_existing_simplified:           0
% 1.14/1.03  inst_num_eq_res_simplified:             0
% 1.14/1.03  inst_num_child_elim:                    0
% 1.14/1.03  inst_num_of_dismatching_blockings:      171
% 1.14/1.03  inst_num_of_non_proper_insts:           597
% 1.14/1.03  inst_num_of_duplicates:                 0
% 1.14/1.03  inst_inst_num_from_inst_to_res:         0
% 1.14/1.03  inst_dismatching_checking_time:         0.
% 1.14/1.03  
% 1.14/1.03  ------ Resolution
% 1.14/1.03  
% 1.14/1.03  res_num_of_clauses:                     0
% 1.14/1.03  res_num_in_passive:                     0
% 1.14/1.03  res_num_in_active:                      0
% 1.14/1.03  res_num_of_loops:                       157
% 1.14/1.03  res_forward_subset_subsumed:            20
% 1.14/1.03  res_backward_subset_subsumed:           2
% 1.14/1.03  res_forward_subsumed:                   2
% 1.14/1.03  res_backward_subsumed:                  0
% 1.14/1.03  res_forward_subsumption_resolution:     4
% 1.14/1.03  res_backward_subsumption_resolution:    0
% 1.14/1.03  res_clause_to_clause_subsumption:       181
% 1.14/1.03  res_orphan_elimination:                 0
% 1.14/1.03  res_tautology_del:                      47
% 1.14/1.03  res_num_eq_res_simplified:              0
% 1.14/1.03  res_num_sel_changes:                    0
% 1.14/1.03  res_moves_from_active_to_pass:          0
% 1.14/1.03  
% 1.14/1.03  ------ Superposition
% 1.14/1.03  
% 1.14/1.03  sup_time_total:                         0.
% 1.14/1.03  sup_time_generating:                    0.
% 1.14/1.03  sup_time_sim_full:                      0.
% 1.14/1.03  sup_time_sim_immed:                     0.
% 1.14/1.03  
% 1.14/1.03  sup_num_of_clauses:                     93
% 1.14/1.03  sup_num_in_active:                      38
% 1.14/1.03  sup_num_in_passive:                     55
% 1.14/1.03  sup_num_of_loops:                       69
% 1.14/1.03  sup_fw_superposition:                   56
% 1.14/1.03  sup_bw_superposition:                   30
% 1.14/1.03  sup_immediate_simplified:               31
% 1.14/1.03  sup_given_eliminated:                   1
% 1.14/1.03  comparisons_done:                       0
% 1.14/1.03  comparisons_avoided:                    8
% 1.14/1.03  
% 1.14/1.03  ------ Simplifications
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  sim_fw_subset_subsumed:                 6
% 1.14/1.03  sim_bw_subset_subsumed:                 3
% 1.14/1.03  sim_fw_subsumed:                        3
% 1.14/1.03  sim_bw_subsumed:                        4
% 1.14/1.03  sim_fw_subsumption_res:                 1
% 1.14/1.03  sim_bw_subsumption_res:                 0
% 1.14/1.03  sim_tautology_del:                      2
% 1.14/1.03  sim_eq_tautology_del:                   5
% 1.14/1.03  sim_eq_res_simp:                        3
% 1.14/1.03  sim_fw_demodulated:                     16
% 1.14/1.03  sim_bw_demodulated:                     29
% 1.14/1.03  sim_light_normalised:                   23
% 1.14/1.03  sim_joinable_taut:                      0
% 1.14/1.03  sim_joinable_simp:                      0
% 1.14/1.03  sim_ac_normalised:                      0
% 1.14/1.03  sim_smt_subsumption:                    0
% 1.14/1.03  
%------------------------------------------------------------------------------
