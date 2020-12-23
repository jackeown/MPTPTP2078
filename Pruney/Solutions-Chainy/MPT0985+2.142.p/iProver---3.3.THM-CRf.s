%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:49 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  193 (3551 expanded)
%              Number of clauses        :  123 (1350 expanded)
%              Number of leaves         :   18 ( 651 expanded)
%              Depth                    :   28
%              Number of atoms          :  556 (16407 expanded)
%              Number of equality atoms :  279 (3512 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f44,plain,
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

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f44])).

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_640,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_642,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_33])).

cnf(c_1671,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1674,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3195,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1671,c_1674])).

cnf(c_3288,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_642,c_3195])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2608,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1678])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_250,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_249])).

cnf(c_308,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_250])).

cnf(c_1669,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_4885,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2608,c_1669])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1677,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5380,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4885,c_1677])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_429,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_430,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_432,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_35])).

cnf(c_1667,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_5385,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5380,c_1667])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3613,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_1678])).

cnf(c_6134,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5385,c_3613])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1673,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2705,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1671,c_1673])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2717,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2705,c_31])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_415,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_416,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_418,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_35])).

cnf(c_1668,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_2730,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2717,c_1668])).

cnf(c_5384,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_5380,c_2730])).

cnf(c_6151,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6134,c_5384])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1934,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1935,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1941,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1942,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_6869,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6151,c_36,c_1935,c_1942,c_5380])).

cnf(c_6874,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3288,c_6869])).

cnf(c_1679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_650,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_651,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_1657,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_5395,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5384,c_1657])).

cnf(c_5914,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5395])).

cnf(c_652,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_5916,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5914,c_36,c_652,c_1935,c_1942,c_2730,c_5380])).

cnf(c_5920,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5916,c_5385])).

cnf(c_5924,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3288,c_5920])).

cnf(c_5929,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1679,c_5924])).

cnf(c_6905,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6874,c_5929])).

cnf(c_6921,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6905,c_2608])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6974,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6921,c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1681,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7218,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6974,c_1681])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_568,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_1661,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1858,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1661,c_5])).

cnf(c_6924,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6905,c_1858])).

cnf(c_6961,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6924])).

cnf(c_6966,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6961,c_5])).

cnf(c_6914,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6905,c_5384])).

cnf(c_7504,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6914,c_1672])).

cnf(c_7508,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7504,c_5385])).

cnf(c_7509,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7508,c_5])).

cnf(c_7702,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6966,c_36,c_1935,c_1942,c_5380,c_7509])).

cnf(c_8091,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7218,c_7702])).

cnf(c_6908,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6905,c_6869])).

cnf(c_7007,plain,
    ( r1_tarski(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6908,c_5])).

cnf(c_7323,plain,
    ( k2_funct_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7007,c_1681])).

cnf(c_8237,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7323,c_7218])).

cnf(c_9012,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8091,c_8237])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1680,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_1666,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2922,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1680,c_1666])).

cnf(c_87,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_89,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1003,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1944,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1945,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_1947,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1945])).

cnf(c_998,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2113,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_2114,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2113])).

cnf(c_3508,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2922,c_89,c_106,c_107,c_1947,c_2114])).

cnf(c_3515,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3508,c_1681])).

cnf(c_3193,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1680,c_1674])).

cnf(c_3518,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3515,c_3193])).

cnf(c_9013,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9012,c_3518])).

cnf(c_9014,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9013])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.10/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/1.00  
% 3.10/1.00  ------  iProver source info
% 3.10/1.00  
% 3.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/1.00  git: non_committed_changes: false
% 3.10/1.00  git: last_make_outside_of_git: false
% 3.10/1.00  
% 3.10/1.00  ------ 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options
% 3.10/1.00  
% 3.10/1.00  --out_options                           all
% 3.10/1.00  --tptp_safe_out                         true
% 3.10/1.00  --problem_path                          ""
% 3.10/1.00  --include_path                          ""
% 3.10/1.00  --clausifier                            res/vclausify_rel
% 3.10/1.00  --clausifier_options                    --mode clausify
% 3.10/1.00  --stdin                                 false
% 3.10/1.00  --stats_out                             all
% 3.10/1.00  
% 3.10/1.00  ------ General Options
% 3.10/1.00  
% 3.10/1.00  --fof                                   false
% 3.10/1.00  --time_out_real                         305.
% 3.10/1.00  --time_out_virtual                      -1.
% 3.10/1.00  --symbol_type_check                     false
% 3.10/1.00  --clausify_out                          false
% 3.10/1.00  --sig_cnt_out                           false
% 3.10/1.00  --trig_cnt_out                          false
% 3.10/1.00  --trig_cnt_out_tolerance                1.
% 3.10/1.00  --trig_cnt_out_sk_spl                   false
% 3.10/1.00  --abstr_cl_out                          false
% 3.10/1.00  
% 3.10/1.00  ------ Global Options
% 3.10/1.00  
% 3.10/1.00  --schedule                              default
% 3.10/1.00  --add_important_lit                     false
% 3.10/1.00  --prop_solver_per_cl                    1000
% 3.10/1.00  --min_unsat_core                        false
% 3.10/1.00  --soft_assumptions                      false
% 3.10/1.00  --soft_lemma_size                       3
% 3.10/1.00  --prop_impl_unit_size                   0
% 3.10/1.00  --prop_impl_unit                        []
% 3.10/1.00  --share_sel_clauses                     true
% 3.10/1.00  --reset_solvers                         false
% 3.10/1.00  --bc_imp_inh                            [conj_cone]
% 3.10/1.00  --conj_cone_tolerance                   3.
% 3.10/1.00  --extra_neg_conj                        none
% 3.10/1.00  --large_theory_mode                     true
% 3.10/1.00  --prolific_symb_bound                   200
% 3.10/1.00  --lt_threshold                          2000
% 3.10/1.00  --clause_weak_htbl                      true
% 3.10/1.00  --gc_record_bc_elim                     false
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing Options
% 3.10/1.00  
% 3.10/1.00  --preprocessing_flag                    true
% 3.10/1.00  --time_out_prep_mult                    0.1
% 3.10/1.00  --splitting_mode                        input
% 3.10/1.00  --splitting_grd                         true
% 3.10/1.00  --splitting_cvd                         false
% 3.10/1.00  --splitting_cvd_svl                     false
% 3.10/1.00  --splitting_nvd                         32
% 3.10/1.00  --sub_typing                            true
% 3.10/1.00  --prep_gs_sim                           true
% 3.10/1.00  --prep_unflatten                        true
% 3.10/1.00  --prep_res_sim                          true
% 3.10/1.00  --prep_upred                            true
% 3.10/1.00  --prep_sem_filter                       exhaustive
% 3.10/1.00  --prep_sem_filter_out                   false
% 3.10/1.00  --pred_elim                             true
% 3.10/1.00  --res_sim_input                         true
% 3.10/1.00  --eq_ax_congr_red                       true
% 3.10/1.00  --pure_diseq_elim                       true
% 3.10/1.00  --brand_transform                       false
% 3.10/1.00  --non_eq_to_eq                          false
% 3.10/1.00  --prep_def_merge                        true
% 3.10/1.00  --prep_def_merge_prop_impl              false
% 3.10/1.00  --prep_def_merge_mbd                    true
% 3.10/1.00  --prep_def_merge_tr_red                 false
% 3.10/1.00  --prep_def_merge_tr_cl                  false
% 3.10/1.00  --smt_preprocessing                     true
% 3.10/1.00  --smt_ac_axioms                         fast
% 3.10/1.00  --preprocessed_out                      false
% 3.10/1.00  --preprocessed_stats                    false
% 3.10/1.00  
% 3.10/1.00  ------ Abstraction refinement Options
% 3.10/1.00  
% 3.10/1.00  --abstr_ref                             []
% 3.10/1.00  --abstr_ref_prep                        false
% 3.10/1.00  --abstr_ref_until_sat                   false
% 3.10/1.00  --abstr_ref_sig_restrict                funpre
% 3.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.00  --abstr_ref_under                       []
% 3.10/1.00  
% 3.10/1.00  ------ SAT Options
% 3.10/1.00  
% 3.10/1.00  --sat_mode                              false
% 3.10/1.00  --sat_fm_restart_options                ""
% 3.10/1.00  --sat_gr_def                            false
% 3.10/1.00  --sat_epr_types                         true
% 3.10/1.00  --sat_non_cyclic_types                  false
% 3.10/1.00  --sat_finite_models                     false
% 3.10/1.00  --sat_fm_lemmas                         false
% 3.10/1.00  --sat_fm_prep                           false
% 3.10/1.00  --sat_fm_uc_incr                        true
% 3.10/1.00  --sat_out_model                         small
% 3.10/1.00  --sat_out_clauses                       false
% 3.10/1.00  
% 3.10/1.00  ------ QBF Options
% 3.10/1.00  
% 3.10/1.00  --qbf_mode                              false
% 3.10/1.00  --qbf_elim_univ                         false
% 3.10/1.00  --qbf_dom_inst                          none
% 3.10/1.00  --qbf_dom_pre_inst                      false
% 3.10/1.00  --qbf_sk_in                             false
% 3.10/1.00  --qbf_pred_elim                         true
% 3.10/1.00  --qbf_split                             512
% 3.10/1.00  
% 3.10/1.00  ------ BMC1 Options
% 3.10/1.00  
% 3.10/1.00  --bmc1_incremental                      false
% 3.10/1.00  --bmc1_axioms                           reachable_all
% 3.10/1.00  --bmc1_min_bound                        0
% 3.10/1.00  --bmc1_max_bound                        -1
% 3.10/1.00  --bmc1_max_bound_default                -1
% 3.10/1.00  --bmc1_symbol_reachability              true
% 3.10/1.00  --bmc1_property_lemmas                  false
% 3.10/1.00  --bmc1_k_induction                      false
% 3.10/1.00  --bmc1_non_equiv_states                 false
% 3.10/1.00  --bmc1_deadlock                         false
% 3.10/1.00  --bmc1_ucm                              false
% 3.10/1.00  --bmc1_add_unsat_core                   none
% 3.10/1.00  --bmc1_unsat_core_children              false
% 3.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.00  --bmc1_out_stat                         full
% 3.10/1.00  --bmc1_ground_init                      false
% 3.10/1.00  --bmc1_pre_inst_next_state              false
% 3.10/1.00  --bmc1_pre_inst_state                   false
% 3.10/1.00  --bmc1_pre_inst_reach_state             false
% 3.10/1.00  --bmc1_out_unsat_core                   false
% 3.10/1.00  --bmc1_aig_witness_out                  false
% 3.10/1.00  --bmc1_verbose                          false
% 3.10/1.00  --bmc1_dump_clauses_tptp                false
% 3.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.00  --bmc1_dump_file                        -
% 3.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.00  --bmc1_ucm_extend_mode                  1
% 3.10/1.00  --bmc1_ucm_init_mode                    2
% 3.10/1.00  --bmc1_ucm_cone_mode                    none
% 3.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.00  --bmc1_ucm_relax_model                  4
% 3.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.00  --bmc1_ucm_layered_model                none
% 3.10/1.00  --bmc1_ucm_max_lemma_size               10
% 3.10/1.00  
% 3.10/1.00  ------ AIG Options
% 3.10/1.00  
% 3.10/1.00  --aig_mode                              false
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation Options
% 3.10/1.00  
% 3.10/1.00  --instantiation_flag                    true
% 3.10/1.00  --inst_sos_flag                         false
% 3.10/1.00  --inst_sos_phase                        true
% 3.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel_side                     num_symb
% 3.10/1.00  --inst_solver_per_active                1400
% 3.10/1.00  --inst_solver_calls_frac                1.
% 3.10/1.00  --inst_passive_queue_type               priority_queues
% 3.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.00  --inst_passive_queues_freq              [25;2]
% 3.10/1.00  --inst_dismatching                      true
% 3.10/1.00  --inst_eager_unprocessed_to_passive     true
% 3.10/1.00  --inst_prop_sim_given                   true
% 3.10/1.00  --inst_prop_sim_new                     false
% 3.10/1.00  --inst_subs_new                         false
% 3.10/1.00  --inst_eq_res_simp                      false
% 3.10/1.00  --inst_subs_given                       false
% 3.10/1.00  --inst_orphan_elimination               true
% 3.10/1.00  --inst_learning_loop_flag               true
% 3.10/1.00  --inst_learning_start                   3000
% 3.10/1.00  --inst_learning_factor                  2
% 3.10/1.00  --inst_start_prop_sim_after_learn       3
% 3.10/1.00  --inst_sel_renew                        solver
% 3.10/1.00  --inst_lit_activity_flag                true
% 3.10/1.00  --inst_restr_to_given                   false
% 3.10/1.00  --inst_activity_threshold               500
% 3.10/1.00  --inst_out_proof                        true
% 3.10/1.00  
% 3.10/1.00  ------ Resolution Options
% 3.10/1.00  
% 3.10/1.00  --resolution_flag                       true
% 3.10/1.00  --res_lit_sel                           adaptive
% 3.10/1.00  --res_lit_sel_side                      none
% 3.10/1.00  --res_ordering                          kbo
% 3.10/1.00  --res_to_prop_solver                    active
% 3.10/1.00  --res_prop_simpl_new                    false
% 3.10/1.00  --res_prop_simpl_given                  true
% 3.10/1.00  --res_passive_queue_type                priority_queues
% 3.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.00  --res_passive_queues_freq               [15;5]
% 3.10/1.00  --res_forward_subs                      full
% 3.10/1.00  --res_backward_subs                     full
% 3.10/1.00  --res_forward_subs_resolution           true
% 3.10/1.00  --res_backward_subs_resolution          true
% 3.10/1.00  --res_orphan_elimination                true
% 3.10/1.00  --res_time_limit                        2.
% 3.10/1.00  --res_out_proof                         true
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Options
% 3.10/1.00  
% 3.10/1.00  --superposition_flag                    true
% 3.10/1.00  --sup_passive_queue_type                priority_queues
% 3.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.00  --demod_completeness_check              fast
% 3.10/1.00  --demod_use_ground                      true
% 3.10/1.00  --sup_to_prop_solver                    passive
% 3.10/1.00  --sup_prop_simpl_new                    true
% 3.10/1.00  --sup_prop_simpl_given                  true
% 3.10/1.00  --sup_fun_splitting                     false
% 3.10/1.00  --sup_smt_interval                      50000
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Simplification Setup
% 3.10/1.00  
% 3.10/1.00  --sup_indices_passive                   []
% 3.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_full_bw                           [BwDemod]
% 3.10/1.00  --sup_immed_triv                        [TrivRules]
% 3.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_immed_bw_main                     []
% 3.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  
% 3.10/1.00  ------ Combination Options
% 3.10/1.00  
% 3.10/1.00  --comb_res_mult                         3
% 3.10/1.00  --comb_sup_mult                         2
% 3.10/1.00  --comb_inst_mult                        10
% 3.10/1.00  
% 3.10/1.00  ------ Debug Options
% 3.10/1.00  
% 3.10/1.00  --dbg_backtrace                         false
% 3.10/1.00  --dbg_dump_prop_clauses                 false
% 3.10/1.00  --dbg_dump_prop_clauses_file            -
% 3.10/1.00  --dbg_out_stat                          false
% 3.10/1.00  ------ Parsing...
% 3.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/1.00  ------ Proving...
% 3.10/1.00  ------ Problem Properties 
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  clauses                                 33
% 3.10/1.00  conjectures                             3
% 3.10/1.00  EPR                                     5
% 3.10/1.00  Horn                                    28
% 3.10/1.00  unary                                   8
% 3.10/1.00  binary                                  8
% 3.10/1.00  lits                                    90
% 3.10/1.00  lits eq                                 37
% 3.10/1.00  fd_pure                                 0
% 3.10/1.00  fd_pseudo                               0
% 3.10/1.00  fd_cond                                 3
% 3.10/1.00  fd_pseudo_cond                          1
% 3.10/1.00  AC symbols                              0
% 3.10/1.00  
% 3.10/1.00  ------ Schedule dynamic 5 is on 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  ------ 
% 3.10/1.00  Current options:
% 3.10/1.00  ------ 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options
% 3.10/1.00  
% 3.10/1.00  --out_options                           all
% 3.10/1.00  --tptp_safe_out                         true
% 3.10/1.00  --problem_path                          ""
% 3.10/1.00  --include_path                          ""
% 3.10/1.00  --clausifier                            res/vclausify_rel
% 3.10/1.00  --clausifier_options                    --mode clausify
% 3.10/1.00  --stdin                                 false
% 3.10/1.00  --stats_out                             all
% 3.10/1.00  
% 3.10/1.00  ------ General Options
% 3.10/1.00  
% 3.10/1.00  --fof                                   false
% 3.10/1.00  --time_out_real                         305.
% 3.10/1.00  --time_out_virtual                      -1.
% 3.10/1.00  --symbol_type_check                     false
% 3.10/1.00  --clausify_out                          false
% 3.10/1.00  --sig_cnt_out                           false
% 3.10/1.00  --trig_cnt_out                          false
% 3.10/1.00  --trig_cnt_out_tolerance                1.
% 3.10/1.00  --trig_cnt_out_sk_spl                   false
% 3.10/1.00  --abstr_cl_out                          false
% 3.10/1.00  
% 3.10/1.00  ------ Global Options
% 3.10/1.00  
% 3.10/1.00  --schedule                              default
% 3.10/1.00  --add_important_lit                     false
% 3.10/1.00  --prop_solver_per_cl                    1000
% 3.10/1.00  --min_unsat_core                        false
% 3.10/1.00  --soft_assumptions                      false
% 3.10/1.00  --soft_lemma_size                       3
% 3.10/1.00  --prop_impl_unit_size                   0
% 3.10/1.00  --prop_impl_unit                        []
% 3.10/1.00  --share_sel_clauses                     true
% 3.10/1.00  --reset_solvers                         false
% 3.10/1.00  --bc_imp_inh                            [conj_cone]
% 3.10/1.00  --conj_cone_tolerance                   3.
% 3.10/1.00  --extra_neg_conj                        none
% 3.10/1.00  --large_theory_mode                     true
% 3.10/1.00  --prolific_symb_bound                   200
% 3.10/1.00  --lt_threshold                          2000
% 3.10/1.00  --clause_weak_htbl                      true
% 3.10/1.00  --gc_record_bc_elim                     false
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing Options
% 3.10/1.00  
% 3.10/1.00  --preprocessing_flag                    true
% 3.10/1.00  --time_out_prep_mult                    0.1
% 3.10/1.00  --splitting_mode                        input
% 3.10/1.00  --splitting_grd                         true
% 3.10/1.00  --splitting_cvd                         false
% 3.10/1.00  --splitting_cvd_svl                     false
% 3.10/1.00  --splitting_nvd                         32
% 3.10/1.00  --sub_typing                            true
% 3.10/1.00  --prep_gs_sim                           true
% 3.10/1.00  --prep_unflatten                        true
% 3.10/1.00  --prep_res_sim                          true
% 3.10/1.00  --prep_upred                            true
% 3.10/1.00  --prep_sem_filter                       exhaustive
% 3.10/1.00  --prep_sem_filter_out                   false
% 3.10/1.00  --pred_elim                             true
% 3.10/1.00  --res_sim_input                         true
% 3.10/1.00  --eq_ax_congr_red                       true
% 3.10/1.00  --pure_diseq_elim                       true
% 3.10/1.00  --brand_transform                       false
% 3.10/1.00  --non_eq_to_eq                          false
% 3.10/1.00  --prep_def_merge                        true
% 3.10/1.00  --prep_def_merge_prop_impl              false
% 3.10/1.00  --prep_def_merge_mbd                    true
% 3.10/1.00  --prep_def_merge_tr_red                 false
% 3.10/1.00  --prep_def_merge_tr_cl                  false
% 3.10/1.00  --smt_preprocessing                     true
% 3.10/1.00  --smt_ac_axioms                         fast
% 3.10/1.00  --preprocessed_out                      false
% 3.10/1.00  --preprocessed_stats                    false
% 3.10/1.00  
% 3.10/1.00  ------ Abstraction refinement Options
% 3.10/1.00  
% 3.10/1.00  --abstr_ref                             []
% 3.10/1.00  --abstr_ref_prep                        false
% 3.10/1.00  --abstr_ref_until_sat                   false
% 3.10/1.00  --abstr_ref_sig_restrict                funpre
% 3.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.00  --abstr_ref_under                       []
% 3.10/1.00  
% 3.10/1.00  ------ SAT Options
% 3.10/1.00  
% 3.10/1.00  --sat_mode                              false
% 3.10/1.00  --sat_fm_restart_options                ""
% 3.10/1.00  --sat_gr_def                            false
% 3.10/1.00  --sat_epr_types                         true
% 3.10/1.00  --sat_non_cyclic_types                  false
% 3.10/1.00  --sat_finite_models                     false
% 3.10/1.00  --sat_fm_lemmas                         false
% 3.10/1.00  --sat_fm_prep                           false
% 3.10/1.00  --sat_fm_uc_incr                        true
% 3.10/1.00  --sat_out_model                         small
% 3.10/1.00  --sat_out_clauses                       false
% 3.10/1.00  
% 3.10/1.00  ------ QBF Options
% 3.10/1.00  
% 3.10/1.00  --qbf_mode                              false
% 3.10/1.00  --qbf_elim_univ                         false
% 3.10/1.00  --qbf_dom_inst                          none
% 3.10/1.00  --qbf_dom_pre_inst                      false
% 3.10/1.00  --qbf_sk_in                             false
% 3.10/1.00  --qbf_pred_elim                         true
% 3.10/1.00  --qbf_split                             512
% 3.10/1.00  
% 3.10/1.00  ------ BMC1 Options
% 3.10/1.00  
% 3.10/1.00  --bmc1_incremental                      false
% 3.10/1.00  --bmc1_axioms                           reachable_all
% 3.10/1.00  --bmc1_min_bound                        0
% 3.10/1.00  --bmc1_max_bound                        -1
% 3.10/1.00  --bmc1_max_bound_default                -1
% 3.10/1.00  --bmc1_symbol_reachability              true
% 3.10/1.00  --bmc1_property_lemmas                  false
% 3.10/1.00  --bmc1_k_induction                      false
% 3.10/1.00  --bmc1_non_equiv_states                 false
% 3.10/1.00  --bmc1_deadlock                         false
% 3.10/1.00  --bmc1_ucm                              false
% 3.10/1.00  --bmc1_add_unsat_core                   none
% 3.10/1.00  --bmc1_unsat_core_children              false
% 3.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.00  --bmc1_out_stat                         full
% 3.10/1.00  --bmc1_ground_init                      false
% 3.10/1.00  --bmc1_pre_inst_next_state              false
% 3.10/1.00  --bmc1_pre_inst_state                   false
% 3.10/1.00  --bmc1_pre_inst_reach_state             false
% 3.10/1.00  --bmc1_out_unsat_core                   false
% 3.10/1.00  --bmc1_aig_witness_out                  false
% 3.10/1.00  --bmc1_verbose                          false
% 3.10/1.00  --bmc1_dump_clauses_tptp                false
% 3.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.00  --bmc1_dump_file                        -
% 3.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.00  --bmc1_ucm_extend_mode                  1
% 3.10/1.00  --bmc1_ucm_init_mode                    2
% 3.10/1.00  --bmc1_ucm_cone_mode                    none
% 3.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.00  --bmc1_ucm_relax_model                  4
% 3.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.00  --bmc1_ucm_layered_model                none
% 3.10/1.00  --bmc1_ucm_max_lemma_size               10
% 3.10/1.00  
% 3.10/1.00  ------ AIG Options
% 3.10/1.00  
% 3.10/1.00  --aig_mode                              false
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation Options
% 3.10/1.00  
% 3.10/1.00  --instantiation_flag                    true
% 3.10/1.00  --inst_sos_flag                         false
% 3.10/1.00  --inst_sos_phase                        true
% 3.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel_side                     none
% 3.10/1.00  --inst_solver_per_active                1400
% 3.10/1.00  --inst_solver_calls_frac                1.
% 3.10/1.00  --inst_passive_queue_type               priority_queues
% 3.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.00  --inst_passive_queues_freq              [25;2]
% 3.10/1.00  --inst_dismatching                      true
% 3.10/1.00  --inst_eager_unprocessed_to_passive     true
% 3.10/1.00  --inst_prop_sim_given                   true
% 3.10/1.00  --inst_prop_sim_new                     false
% 3.10/1.00  --inst_subs_new                         false
% 3.10/1.00  --inst_eq_res_simp                      false
% 3.10/1.00  --inst_subs_given                       false
% 3.10/1.00  --inst_orphan_elimination               true
% 3.10/1.00  --inst_learning_loop_flag               true
% 3.10/1.00  --inst_learning_start                   3000
% 3.10/1.00  --inst_learning_factor                  2
% 3.10/1.00  --inst_start_prop_sim_after_learn       3
% 3.10/1.00  --inst_sel_renew                        solver
% 3.10/1.00  --inst_lit_activity_flag                true
% 3.10/1.00  --inst_restr_to_given                   false
% 3.10/1.00  --inst_activity_threshold               500
% 3.10/1.00  --inst_out_proof                        true
% 3.10/1.00  
% 3.10/1.00  ------ Resolution Options
% 3.10/1.00  
% 3.10/1.00  --resolution_flag                       false
% 3.10/1.00  --res_lit_sel                           adaptive
% 3.10/1.00  --res_lit_sel_side                      none
% 3.10/1.00  --res_ordering                          kbo
% 3.10/1.00  --res_to_prop_solver                    active
% 3.10/1.00  --res_prop_simpl_new                    false
% 3.10/1.00  --res_prop_simpl_given                  true
% 3.10/1.00  --res_passive_queue_type                priority_queues
% 3.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.00  --res_passive_queues_freq               [15;5]
% 3.10/1.00  --res_forward_subs                      full
% 3.10/1.00  --res_backward_subs                     full
% 3.10/1.00  --res_forward_subs_resolution           true
% 3.10/1.00  --res_backward_subs_resolution          true
% 3.10/1.00  --res_orphan_elimination                true
% 3.10/1.00  --res_time_limit                        2.
% 3.10/1.00  --res_out_proof                         true
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Options
% 3.10/1.00  
% 3.10/1.00  --superposition_flag                    true
% 3.10/1.00  --sup_passive_queue_type                priority_queues
% 3.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.00  --demod_completeness_check              fast
% 3.10/1.00  --demod_use_ground                      true
% 3.10/1.00  --sup_to_prop_solver                    passive
% 3.10/1.00  --sup_prop_simpl_new                    true
% 3.10/1.00  --sup_prop_simpl_given                  true
% 3.10/1.00  --sup_fun_splitting                     false
% 3.10/1.00  --sup_smt_interval                      50000
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Simplification Setup
% 3.10/1.00  
% 3.10/1.00  --sup_indices_passive                   []
% 3.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_full_bw                           [BwDemod]
% 3.10/1.00  --sup_immed_triv                        [TrivRules]
% 3.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_immed_bw_main                     []
% 3.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  
% 3.10/1.00  ------ Combination Options
% 3.10/1.00  
% 3.10/1.00  --comb_res_mult                         3
% 3.10/1.00  --comb_sup_mult                         2
% 3.10/1.00  --comb_inst_mult                        10
% 3.10/1.00  
% 3.10/1.00  ------ Debug Options
% 3.10/1.00  
% 3.10/1.00  --dbg_backtrace                         false
% 3.10/1.00  --dbg_dump_prop_clauses                 false
% 3.10/1.00  --dbg_dump_prop_clauses_file            -
% 3.10/1.00  --dbg_out_stat                          false
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  ------ Proving...
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  % SZS status Theorem for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00   Resolution empty clause
% 3.10/1.00  
% 3.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  fof(f15,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f31,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f15])).
% 3.10/1.00  
% 3.10/1.00  fof(f32,plain,(
% 3.10/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(flattening,[],[f31])).
% 3.10/1.00  
% 3.10/1.00  fof(f43,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(nnf_transformation,[],[f32])).
% 3.10/1.00  
% 3.10/1.00  fof(f67,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f43])).
% 3.10/1.00  
% 3.10/1.00  fof(f17,conjecture,(
% 3.10/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f18,negated_conjecture,(
% 3.10/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.10/1.00    inference(negated_conjecture,[],[f17])).
% 3.10/1.00  
% 3.10/1.00  fof(f35,plain,(
% 3.10/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.10/1.00    inference(ennf_transformation,[],[f18])).
% 3.10/1.00  
% 3.10/1.00  fof(f36,plain,(
% 3.10/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.10/1.00    inference(flattening,[],[f35])).
% 3.10/1.00  
% 3.10/1.00  fof(f44,plain,(
% 3.10/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f45,plain,(
% 3.10/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f44])).
% 3.10/1.00  
% 3.10/1.00  fof(f77,plain,(
% 3.10/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.10/1.00    inference(cnf_transformation,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f78,plain,(
% 3.10/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.10/1.00    inference(cnf_transformation,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f13,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f29,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f13])).
% 3.10/1.00  
% 3.10/1.00  fof(f65,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f29])).
% 3.10/1.00  
% 3.10/1.00  fof(f5,axiom,(
% 3.10/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f41,plain,(
% 3.10/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.10/1.00    inference(nnf_transformation,[],[f5])).
% 3.10/1.00  
% 3.10/1.00  fof(f54,plain,(
% 3.10/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f7,axiom,(
% 3.10/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f22,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f7])).
% 3.10/1.00  
% 3.10/1.00  fof(f56,plain,(
% 3.10/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f22])).
% 3.10/1.00  
% 3.10/1.00  fof(f55,plain,(
% 3.10/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f9,axiom,(
% 3.10/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f59,plain,(
% 3.10/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f9])).
% 3.10/1.00  
% 3.10/1.00  fof(f11,axiom,(
% 3.10/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f26,plain,(
% 3.10/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f11])).
% 3.10/1.00  
% 3.10/1.00  fof(f27,plain,(
% 3.10/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.10/1.00    inference(flattening,[],[f26])).
% 3.10/1.00  
% 3.10/1.00  fof(f63,plain,(
% 3.10/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f27])).
% 3.10/1.00  
% 3.10/1.00  fof(f79,plain,(
% 3.10/1.00    v2_funct_1(sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f76,plain,(
% 3.10/1.00    v1_funct_1(sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f16,axiom,(
% 3.10/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f33,plain,(
% 3.10/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f16])).
% 3.10/1.00  
% 3.10/1.00  fof(f34,plain,(
% 3.10/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.10/1.00    inference(flattening,[],[f33])).
% 3.10/1.00  
% 3.10/1.00  fof(f75,plain,(
% 3.10/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f34])).
% 3.10/1.00  
% 3.10/1.00  fof(f14,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f30,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f14])).
% 3.10/1.00  
% 3.10/1.00  fof(f66,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f30])).
% 3.10/1.00  
% 3.10/1.00  fof(f80,plain,(
% 3.10/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.10/1.00    inference(cnf_transformation,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f62,plain,(
% 3.10/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f27])).
% 3.10/1.00  
% 3.10/1.00  fof(f10,axiom,(
% 3.10/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f24,plain,(
% 3.10/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f10])).
% 3.10/1.00  
% 3.10/1.00  fof(f25,plain,(
% 3.10/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.10/1.00    inference(flattening,[],[f24])).
% 3.10/1.00  
% 3.10/1.00  fof(f61,plain,(
% 3.10/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f25])).
% 3.10/1.00  
% 3.10/1.00  fof(f60,plain,(
% 3.10/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f25])).
% 3.10/1.00  
% 3.10/1.00  fof(f74,plain,(
% 3.10/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f34])).
% 3.10/1.00  
% 3.10/1.00  fof(f81,plain,(
% 3.10/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.10/1.00    inference(cnf_transformation,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f3,axiom,(
% 3.10/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f39,plain,(
% 3.10/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/1.00    inference(nnf_transformation,[],[f3])).
% 3.10/1.00  
% 3.10/1.00  fof(f40,plain,(
% 3.10/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/1.00    inference(flattening,[],[f39])).
% 3.10/1.00  
% 3.10/1.00  fof(f52,plain,(
% 3.10/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.10/1.00    inference(cnf_transformation,[],[f40])).
% 3.10/1.00  
% 3.10/1.00  fof(f84,plain,(
% 3.10/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.10/1.00    inference(equality_resolution,[],[f52])).
% 3.10/1.00  
% 3.10/1.00  fof(f2,axiom,(
% 3.10/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f21,plain,(
% 3.10/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.10/1.00    inference(ennf_transformation,[],[f2])).
% 3.10/1.00  
% 3.10/1.00  fof(f49,plain,(
% 3.10/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f21])).
% 3.10/1.00  
% 3.10/1.00  fof(f70,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f43])).
% 3.10/1.00  
% 3.10/1.00  fof(f89,plain,(
% 3.10/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.10/1.00    inference(equality_resolution,[],[f70])).
% 3.10/1.00  
% 3.10/1.00  fof(f51,plain,(
% 3.10/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.10/1.00    inference(cnf_transformation,[],[f40])).
% 3.10/1.00  
% 3.10/1.00  fof(f85,plain,(
% 3.10/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.10/1.00    inference(equality_resolution,[],[f51])).
% 3.10/1.00  
% 3.10/1.00  fof(f4,axiom,(
% 3.10/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f53,plain,(
% 3.10/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f4])).
% 3.10/1.00  
% 3.10/1.00  fof(f12,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f19,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.10/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.10/1.00  
% 3.10/1.00  fof(f28,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f19])).
% 3.10/1.00  
% 3.10/1.00  fof(f64,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f28])).
% 3.10/1.00  
% 3.10/1.00  fof(f8,axiom,(
% 3.10/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f23,plain,(
% 3.10/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.10/1.00    inference(ennf_transformation,[],[f8])).
% 3.10/1.00  
% 3.10/1.00  fof(f42,plain,(
% 3.10/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.10/1.00    inference(nnf_transformation,[],[f23])).
% 3.10/1.00  
% 3.10/1.00  fof(f57,plain,(
% 3.10/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f42])).
% 3.10/1.00  
% 3.10/1.00  fof(f50,plain,(
% 3.10/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f40])).
% 3.10/1.00  
% 3.10/1.00  cnf(c_26,plain,
% 3.10/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.10/1.00      | k1_xboole_0 = X2 ),
% 3.10/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_34,negated_conjecture,
% 3.10/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_639,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.10/1.00      | sK0 != X1
% 3.10/1.00      | sK1 != X2
% 3.10/1.00      | sK2 != X0
% 3.10/1.00      | k1_xboole_0 = X2 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_640,plain,
% 3.10/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.10/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.10/1.00      | k1_xboole_0 = sK1 ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_639]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_33,negated_conjecture,
% 3.10/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.10/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_642,plain,
% 3.10/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.10/1.00      inference(global_propositional_subsumption,[status(thm)],[c_640,c_33]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1671,plain,
% 3.10/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_19,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1674,plain,
% 3.10/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.10/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3195,plain,
% 3.10/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1671,c_1674]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3288,plain,
% 3.10/1.00      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_642,c_3195]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_9,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1678,plain,
% 3.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.10/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2608,plain,
% 3.10/1.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1671,c_1678]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8,plain,
% 3.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_249,plain,
% 3.10/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.10/1.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_250,plain,
% 3.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_249]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_308,plain,
% 3.10/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.10/1.00      inference(bin_hyper_res,[status(thm)],[c_10,c_250]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1669,plain,
% 3.10/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.10/1.00      | v1_relat_1(X1) != iProver_top
% 3.10/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4885,plain,
% 3.10/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.10/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2608,c_1669]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_13,plain,
% 3.10/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1677,plain,
% 3.10/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5380,plain,
% 3.10/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.10/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4885,c_1677]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_16,plain,
% 3.10/1.00      ( ~ v2_funct_1(X0)
% 3.10/1.00      | ~ v1_funct_1(X0)
% 3.10/1.00      | ~ v1_relat_1(X0)
% 3.10/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_32,negated_conjecture,
% 3.10/1.00      ( v2_funct_1(sK2) ),
% 3.10/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_429,plain,
% 3.10/1.00      ( ~ v1_funct_1(X0)
% 3.10/1.00      | ~ v1_relat_1(X0)
% 3.10/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.10/1.00      | sK2 != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_430,plain,
% 3.10/1.00      ( ~ v1_funct_1(sK2)
% 3.10/1.00      | ~ v1_relat_1(sK2)
% 3.10/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_429]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_35,negated_conjecture,
% 3.10/1.00      ( v1_funct_1(sK2) ),
% 3.10/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_432,plain,
% 3.10/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.10/1.00      inference(global_propositional_subsumption,[status(thm)],[c_430,c_35]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1667,plain,
% 3.10/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.10/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5385,plain,
% 3.10/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5380,c_1667]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_27,plain,
% 3.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.10/1.00      | ~ v1_funct_1(X0)
% 3.10/1.00      | ~ v1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1672,plain,
% 3.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.10/1.00      | v1_funct_1(X0) != iProver_top
% 3.10/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3613,plain,
% 3.10/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 3.10/1.00      | v1_funct_1(X0) != iProver_top
% 3.10/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1672,c_1678]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6134,plain,
% 3.10/1.00      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))) = iProver_top
% 3.10/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5385,c_3613]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_20,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1673,plain,
% 3.10/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.10/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2705,plain,
% 3.10/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_1671,c_1673]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_31,negated_conjecture,
% 3.10/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.10/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2717,plain,
% 3.10/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.10/1.00      inference(light_normalisation,[status(thm)],[c_2705,c_31]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_17,plain,
% 3.10/1.00      ( ~ v2_funct_1(X0)
% 3.10/1.00      | ~ v1_funct_1(X0)
% 3.10/1.00      | ~ v1_relat_1(X0)
% 3.10/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_415,plain,
% 3.10/1.00      ( ~ v1_funct_1(X0)
% 3.10/1.00      | ~ v1_relat_1(X0)
% 3.10/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.10/1.00      | sK2 != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_416,plain,
% 3.10/1.00      ( ~ v1_funct_1(sK2)
% 3.10/1.00      | ~ v1_relat_1(sK2)
% 3.10/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_415]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_418,plain,
% 3.10/1.00      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.10/1.00      inference(global_propositional_subsumption,[status(thm)],[c_416,c_35]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1668,plain,
% 3.10/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.10/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2730,plain,
% 3.10/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 | v1_relat_1(sK2) != iProver_top ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_2717,c_1668]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5384,plain,
% 3.10/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5380,c_2730]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6151,plain,
% 3.10/1.00      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top
% 3.10/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.00      inference(light_normalisation,[status(thm)],[c_6134,c_5384]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_36,plain,
% 3.10/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_14,plain,
% 3.10/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1934,plain,
% 3.10/1.00      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1935,plain,
% 3.10/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.10/1.00      | v1_funct_1(sK2) != iProver_top
% 3.10/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_15,plain,
% 3.10/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1941,plain,
% 3.10/1.00      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1942,plain,
% 3.10/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.10/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.10/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6869,plain,
% 3.10/1.00      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_6151,c_36,c_1935,c_1942,c_5380]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6874,plain,
% 3.10/1.00      ( sK1 = k1_xboole_0
% 3.10/1.00      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3288,c_6869]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1679,plain,
% 3.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.10/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_28,plain,
% 3.10/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.10/1.01      | ~ v1_funct_1(X0)
% 3.10/1.01      | ~ v1_relat_1(X0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_30,negated_conjecture,
% 3.10/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.10/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.10/1.01      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_650,plain,
% 3.10/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.10/1.01      | ~ v1_funct_1(X0)
% 3.10/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.10/1.01      | ~ v1_relat_1(X0)
% 3.10/1.01      | k2_relat_1(X0) != sK0
% 3.10/1.01      | k2_funct_1(sK2) != X0
% 3.10/1.01      | k1_relat_1(X0) != sK1 ),
% 3.10/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_651,plain,
% 3.10/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.10/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.10/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.10/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.10/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.10/1.01      inference(unflattening,[status(thm)],[c_650]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1657,plain,
% 3.10/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.10/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5395,plain,
% 3.10/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.10/1.01      | sK1 != sK1
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_5384,c_1657]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5914,plain,
% 3.10/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_5395]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_652,plain,
% 3.10/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.10/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5916,plain,
% 3.10/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.10/1.01      inference(global_propositional_subsumption,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_5914,c_36,c_652,c_1935,c_1942,c_2730,c_5380]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5920,plain,
% 3.10/1.01      ( k1_relat_1(sK2) != sK0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.10/1.01      inference(light_normalisation,[status(thm)],[c_5916,c_5385]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5924,plain,
% 3.10/1.01      ( sK1 = k1_xboole_0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_3288,c_5920]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5929,plain,
% 3.10/1.01      ( sK1 = k1_xboole_0
% 3.10/1.01      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1679,c_5924]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6905,plain,
% 3.10/1.01      ( sK1 = k1_xboole_0 ),
% 3.10/1.01      inference(global_propositional_subsumption,[status(thm)],[c_6874,c_5929]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6921,plain,
% 3.10/1.01      ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_6905,c_2608]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_4,plain,
% 3.10/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.10/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6974,plain,
% 3.10/1.01      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_6921,c_4]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.10/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1681,plain,
% 3.10/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7218,plain,
% 3.10/1.01      ( sK2 = k1_xboole_0 ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_6974,c_1681]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_23,plain,
% 3.10/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.10/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.10/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_567,plain,
% 3.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.10/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.10/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.10/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.10/1.01      | k2_funct_1(sK2) != X0
% 3.10/1.01      | sK0 != X1
% 3.10/1.01      | sK1 != k1_xboole_0 ),
% 3.10/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_568,plain,
% 3.10/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.10/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.10/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.10/1.01      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.10/1.01      | sK1 != k1_xboole_0 ),
% 3.10/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1661,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.10/1.01      | sK1 != k1_xboole_0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5,plain,
% 3.10/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.10/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1858,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.10/1.01      | sK1 != k1_xboole_0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_1661,c_5]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6924,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.10/1.01      | k1_xboole_0 != k1_xboole_0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_6905,c_1858]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6961,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_6924]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6966,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.10/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_6961,c_5]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6914,plain,
% 3.10/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_6905,c_5384]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7504,plain,
% 3.10/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_6914,c_1672]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7508,plain,
% 3.10/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(light_normalisation,[status(thm)],[c_7504,c_5385]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7509,plain,
% 3.10/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.10/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.10/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_7508,c_5]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7702,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.10/1.01      inference(global_propositional_subsumption,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_6966,c_36,c_1935,c_1942,c_5380,c_7509]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8091,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_7218,c_7702]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6908,plain,
% 3.10/1.01      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))) = iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_6905,c_6869]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7007,plain,
% 3.10/1.01      ( r1_tarski(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_6908,c_5]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7323,plain,
% 3.10/1.01      ( k2_funct_1(sK2) = k1_xboole_0 ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_7007,c_1681]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8237,plain,
% 3.10/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.10/1.01      inference(light_normalisation,[status(thm)],[c_7323,c_7218]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_9012,plain,
% 3.10/1.01      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.10/1.01      inference(light_normalisation,[status(thm)],[c_8091,c_8237]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7,plain,
% 3.10/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1680,plain,
% 3.10/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_18,plain,
% 3.10/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.10/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_12,plain,
% 3.10/1.01      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_449,plain,
% 3.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.10/1.01      | ~ v1_relat_1(X0) ),
% 3.10/1.01      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1666,plain,
% 3.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.10/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.10/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2922,plain,
% 3.10/1.01      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 3.10/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1680,c_1666]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_87,plain,
% 3.10/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_89,plain,
% 3.10/1.01      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_87]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6,plain,
% 3.10/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.10/1.01      | k1_xboole_0 = X0
% 3.10/1.01      | k1_xboole_0 = X1 ),
% 3.10/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_106,plain,
% 3.10/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.10/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_107,plain,
% 3.10/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1003,plain,
% 3.10/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.10/1.01      theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1944,plain,
% 3.10/1.01      ( v1_relat_1(X0)
% 3.10/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 3.10/1.01      | X0 != k2_zfmisc_1(X1,X2) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1003]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1945,plain,
% 3.10/1.01      ( X0 != k2_zfmisc_1(X1,X2)
% 3.10/1.01      | v1_relat_1(X0) = iProver_top
% 3.10/1.01      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1947,plain,
% 3.10/1.01      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.10/1.01      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.10/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1945]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_998,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2113,plain,
% 3.10/1.01      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_998]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2114,plain,
% 3.10/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.10/1.01      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.10/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_2113]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3508,plain,
% 3.10/1.01      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.10/1.01      inference(global_propositional_subsumption,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_2922,c_89,c_106,c_107,c_1947,c_2114]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3515,plain,
% 3.10/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_3508,c_1681]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3193,plain,
% 3.10/1.01      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1680,c_1674]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3518,plain,
% 3.10/1.01      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_3515,c_3193]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_9013,plain,
% 3.10/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_9012,c_3518]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_9014,plain,
% 3.10/1.01      ( $false ),
% 3.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_9013]) ).
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  ------                               Statistics
% 3.10/1.01  
% 3.10/1.01  ------ General
% 3.10/1.01  
% 3.10/1.01  abstr_ref_over_cycles:                  0
% 3.10/1.01  abstr_ref_under_cycles:                 0
% 3.10/1.01  gc_basic_clause_elim:                   0
% 3.10/1.01  forced_gc_time:                         0
% 3.10/1.01  parsing_time:                           0.033
% 3.10/1.01  unif_index_cands_time:                  0.
% 3.10/1.01  unif_index_add_time:                    0.
% 3.10/1.01  orderings_time:                         0.
% 3.10/1.01  out_proof_time:                         0.013
% 3.10/1.01  total_time:                             0.302
% 3.10/1.01  num_of_symbols:                         49
% 3.10/1.01  num_of_terms:                           5987
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing
% 3.10/1.01  
% 3.10/1.01  num_of_splits:                          0
% 3.10/1.01  num_of_split_atoms:                     0
% 3.10/1.01  num_of_reused_defs:                     0
% 3.10/1.01  num_eq_ax_congr_red:                    4
% 3.10/1.01  num_of_sem_filtered_clauses:            1
% 3.10/1.01  num_of_subtypes:                        0
% 3.10/1.01  monotx_restored_types:                  0
% 3.10/1.01  sat_num_of_epr_types:                   0
% 3.10/1.01  sat_num_of_non_cyclic_types:            0
% 3.10/1.01  sat_guarded_non_collapsed_types:        0
% 3.10/1.01  num_pure_diseq_elim:                    0
% 3.10/1.01  simp_replaced_by:                       0
% 3.10/1.01  res_preprocessed:                       160
% 3.10/1.01  prep_upred:                             0
% 3.10/1.01  prep_unflattend:                        43
% 3.10/1.01  smt_new_axioms:                         0
% 3.10/1.01  pred_elim_cands:                        4
% 3.10/1.01  pred_elim:                              3
% 3.10/1.01  pred_elim_cl:                           1
% 3.10/1.01  pred_elim_cycles:                       5
% 3.10/1.01  merged_defs:                            8
% 3.10/1.01  merged_defs_ncl:                        0
% 3.10/1.01  bin_hyper_res:                          9
% 3.10/1.01  prep_cycles:                            4
% 3.10/1.01  pred_elim_time:                         0.024
% 3.10/1.01  splitting_time:                         0.
% 3.10/1.01  sem_filter_time:                        0.
% 3.10/1.01  monotx_time:                            0.
% 3.10/1.01  subtype_inf_time:                       0.
% 3.10/1.01  
% 3.10/1.01  ------ Problem properties
% 3.10/1.01  
% 3.10/1.01  clauses:                                33
% 3.10/1.01  conjectures:                            3
% 3.10/1.01  epr:                                    5
% 3.10/1.01  horn:                                   28
% 3.10/1.01  ground:                                 13
% 3.10/1.01  unary:                                  8
% 3.10/1.01  binary:                                 8
% 3.10/1.01  lits:                                   90
% 3.10/1.01  lits_eq:                                37
% 3.10/1.01  fd_pure:                                0
% 3.10/1.01  fd_pseudo:                              0
% 3.10/1.01  fd_cond:                                3
% 3.10/1.01  fd_pseudo_cond:                         1
% 3.10/1.01  ac_symbols:                             0
% 3.10/1.01  
% 3.10/1.01  ------ Propositional Solver
% 3.10/1.01  
% 3.10/1.01  prop_solver_calls:                      30
% 3.10/1.01  prop_fast_solver_calls:                 1301
% 3.10/1.01  smt_solver_calls:                       0
% 3.10/1.01  smt_fast_solver_calls:                  0
% 3.10/1.01  prop_num_of_clauses:                    2808
% 3.10/1.01  prop_preprocess_simplified:             7700
% 3.10/1.01  prop_fo_subsumed:                       51
% 3.10/1.01  prop_solver_time:                       0.
% 3.10/1.01  smt_solver_time:                        0.
% 3.10/1.01  smt_fast_solver_time:                   0.
% 3.10/1.01  prop_fast_solver_time:                  0.
% 3.10/1.01  prop_unsat_core_time:                   0.
% 3.10/1.01  
% 3.10/1.01  ------ QBF
% 3.10/1.01  
% 3.10/1.01  qbf_q_res:                              0
% 3.10/1.01  qbf_num_tautologies:                    0
% 3.10/1.01  qbf_prep_cycles:                        0
% 3.10/1.01  
% 3.10/1.01  ------ BMC1
% 3.10/1.01  
% 3.10/1.01  bmc1_current_bound:                     -1
% 3.10/1.01  bmc1_last_solved_bound:                 -1
% 3.10/1.01  bmc1_unsat_core_size:                   -1
% 3.10/1.01  bmc1_unsat_core_parents_size:           -1
% 3.10/1.01  bmc1_merge_next_fun:                    0
% 3.10/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.10/1.01  
% 3.10/1.01  ------ Instantiation
% 3.10/1.01  
% 3.10/1.01  inst_num_of_clauses:                    958
% 3.10/1.01  inst_num_in_passive:                    327
% 3.10/1.01  inst_num_in_active:                     507
% 3.10/1.01  inst_num_in_unprocessed:                126
% 3.10/1.01  inst_num_of_loops:                      650
% 3.10/1.01  inst_num_of_learning_restarts:          0
% 3.10/1.01  inst_num_moves_active_passive:          139
% 3.10/1.01  inst_lit_activity:                      0
% 3.10/1.01  inst_lit_activity_moves:                0
% 3.10/1.01  inst_num_tautologies:                   0
% 3.10/1.01  inst_num_prop_implied:                  0
% 3.10/1.01  inst_num_existing_simplified:           0
% 3.10/1.01  inst_num_eq_res_simplified:             0
% 3.10/1.01  inst_num_child_elim:                    0
% 3.10/1.01  inst_num_of_dismatching_blockings:      473
% 3.10/1.01  inst_num_of_non_proper_insts:           1164
% 3.10/1.01  inst_num_of_duplicates:                 0
% 3.10/1.01  inst_inst_num_from_inst_to_res:         0
% 3.10/1.01  inst_dismatching_checking_time:         0.
% 3.10/1.01  
% 3.10/1.01  ------ Resolution
% 3.10/1.01  
% 3.10/1.01  res_num_of_clauses:                     0
% 3.10/1.01  res_num_in_passive:                     0
% 3.10/1.01  res_num_in_active:                      0
% 3.10/1.01  res_num_of_loops:                       164
% 3.10/1.01  res_forward_subset_subsumed:            54
% 3.10/1.01  res_backward_subset_subsumed:           4
% 3.10/1.01  res_forward_subsumed:                   0
% 3.10/1.01  res_backward_subsumed:                  0
% 3.10/1.01  res_forward_subsumption_resolution:     1
% 3.10/1.01  res_backward_subsumption_resolution:    0
% 3.10/1.01  res_clause_to_clause_subsumption:       625
% 3.10/1.01  res_orphan_elimination:                 0
% 3.10/1.01  res_tautology_del:                      77
% 3.10/1.01  res_num_eq_res_simplified:              0
% 3.10/1.01  res_num_sel_changes:                    0
% 3.10/1.01  res_moves_from_active_to_pass:          0
% 3.10/1.01  
% 3.10/1.01  ------ Superposition
% 3.10/1.01  
% 3.10/1.01  sup_time_total:                         0.
% 3.10/1.01  sup_time_generating:                    0.
% 3.10/1.01  sup_time_sim_full:                      0.
% 3.10/1.01  sup_time_sim_immed:                     0.
% 3.10/1.01  
% 3.10/1.01  sup_num_of_clauses:                     100
% 3.10/1.01  sup_num_in_active:                      63
% 3.10/1.01  sup_num_in_passive:                     37
% 3.10/1.01  sup_num_of_loops:                       129
% 3.10/1.01  sup_fw_superposition:                   144
% 3.10/1.01  sup_bw_superposition:                   117
% 3.10/1.01  sup_immediate_simplified:               122
% 3.10/1.01  sup_given_eliminated:                   2
% 3.10/1.01  comparisons_done:                       0
% 3.10/1.01  comparisons_avoided:                    8
% 3.10/1.01  
% 3.10/1.01  ------ Simplifications
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  sim_fw_subset_subsumed:                 27
% 3.10/1.01  sim_bw_subset_subsumed:                 16
% 3.10/1.01  sim_fw_subsumed:                        35
% 3.10/1.01  sim_bw_subsumed:                        4
% 3.10/1.01  sim_fw_subsumption_res:                 4
% 3.10/1.01  sim_bw_subsumption_res:                 1
% 3.10/1.01  sim_tautology_del:                      10
% 3.10/1.01  sim_eq_tautology_del:                   30
% 3.10/1.01  sim_eq_res_simp:                        3
% 3.10/1.01  sim_fw_demodulated:                     49
% 3.10/1.01  sim_bw_demodulated:                     64
% 3.10/1.01  sim_light_normalised:                   74
% 3.10/1.01  sim_joinable_taut:                      0
% 3.10/1.01  sim_joinable_simp:                      0
% 3.10/1.01  sim_ac_normalised:                      0
% 3.10/1.01  sim_smt_subsumption:                    0
% 3.10/1.01  
%------------------------------------------------------------------------------
