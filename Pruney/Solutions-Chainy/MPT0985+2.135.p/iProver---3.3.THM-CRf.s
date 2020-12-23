%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:47 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  184 (4961 expanded)
%              Number of clauses        :  122 (1725 expanded)
%              Number of leaves         :   17 ( 941 expanded)
%              Depth                    :   25
%              Number of atoms          :  554 (25424 expanded)
%              Number of equality atoms :  285 (5485 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f37,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f18])).

fof(f51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_611,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_613,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_30])).

cnf(c_1407,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1410,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2836,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1407,c_1410])).

cnf(c_2929,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_613,c_2836])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1411,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2051,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_1411])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_384,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_385,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_387,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_32])).

cnf(c_1403,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_2131,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2051,c_1403])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1408,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3561,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_1408])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_370,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_371,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_373,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_32])).

cnf(c_1404,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_2130,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2051,c_1404])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1409,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2282,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1407,c_1409])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2284,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2282,c_28])).

cnf(c_2448,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2130,c_2284])).

cnf(c_3574,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3561,c_2448])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1665,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1666,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1665])).

cnf(c_1668,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1800,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_1801,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_3725,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3574,c_33,c_35,c_1666,c_1801])).

cnf(c_3731,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_3725])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1414,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1417,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2467,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_1417])).

cnf(c_3303,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_2467])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_621,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_622,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_634,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_622,c_12])).

cnf(c_1393,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_639,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_1958,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1393,c_33,c_35,c_639,c_1666,c_1801])).

cnf(c_1959,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1958])).

cnf(c_2450,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2448,c_1959])).

cnf(c_2457,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2450])).

cnf(c_3291,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2457,c_2131])).

cnf(c_11,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_94,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_927,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1887,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_2201,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_2203,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2201])).

cnf(c_931,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2202,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_2204,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_2291,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2284,c_1417])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_324,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_325,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_640,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_27])).

cnf(c_641,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_653,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_641,c_12])).

cnf(c_1392,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_658,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1804,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1392,c_33,c_35,c_658,c_1666,c_1801])).

cnf(c_1805,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1804])).

cnf(c_2451,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2448,c_1805])).

cnf(c_2452,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2451])).

cnf(c_2639,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2452,c_2131])).

cnf(c_2858,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_2859,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_3295,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3291,c_35,c_11,c_94,c_3,c_1801,c_2203,c_2204,c_2291,c_2639,c_2859,c_2929])).

cnf(c_3987,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_35,c_11,c_94,c_3,c_1801,c_2203,c_2204,c_2291,c_2639,c_2859,c_2929,c_3291,c_3731])).

cnf(c_3993,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_3987])).

cnf(c_3996,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3731,c_33,c_35,c_1801,c_3993])).

cnf(c_4010,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3996,c_2639])).

cnf(c_2307,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2291])).

cnf(c_2399,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2291,c_30,c_1800,c_2307])).

cnf(c_2400,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2399])).

cnf(c_4015,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3996,c_2400])).

cnf(c_4064,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4015])).

cnf(c_4108,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4010,c_4064])).

cnf(c_4111,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4108,c_3])).

cnf(c_4112,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4111])).

cnf(c_1416,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2464,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2448,c_1416])).

cnf(c_4012,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3996,c_2464])).

cnf(c_4094,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4012])).

cnf(c_4095,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4094,c_4064])).

cnf(c_79,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_80,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_87,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_89,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_4733,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4095,c_79,c_80,c_89])).

cnf(c_5067,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4112,c_4733])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1418,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5069,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5067,c_1418])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.67/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.99  
% 2.67/0.99  ------  iProver source info
% 2.67/0.99  
% 2.67/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.99  git: non_committed_changes: false
% 2.67/0.99  git: last_make_outside_of_git: false
% 2.67/0.99  
% 2.67/0.99  ------ 
% 2.67/0.99  
% 2.67/0.99  ------ Input Options
% 2.67/0.99  
% 2.67/0.99  --out_options                           all
% 2.67/0.99  --tptp_safe_out                         true
% 2.67/0.99  --problem_path                          ""
% 2.67/0.99  --include_path                          ""
% 2.67/0.99  --clausifier                            res/vclausify_rel
% 2.67/0.99  --clausifier_options                    --mode clausify
% 2.67/0.99  --stdin                                 false
% 2.67/0.99  --stats_out                             all
% 2.67/0.99  
% 2.67/0.99  ------ General Options
% 2.67/0.99  
% 2.67/0.99  --fof                                   false
% 2.67/0.99  --time_out_real                         305.
% 2.67/0.99  --time_out_virtual                      -1.
% 2.67/0.99  --symbol_type_check                     false
% 2.67/0.99  --clausify_out                          false
% 2.67/0.99  --sig_cnt_out                           false
% 2.67/0.99  --trig_cnt_out                          false
% 2.67/0.99  --trig_cnt_out_tolerance                1.
% 2.67/0.99  --trig_cnt_out_sk_spl                   false
% 2.67/0.99  --abstr_cl_out                          false
% 2.67/0.99  
% 2.67/0.99  ------ Global Options
% 2.67/0.99  
% 2.67/0.99  --schedule                              default
% 2.67/0.99  --add_important_lit                     false
% 2.67/0.99  --prop_solver_per_cl                    1000
% 2.67/0.99  --min_unsat_core                        false
% 2.67/0.99  --soft_assumptions                      false
% 2.67/0.99  --soft_lemma_size                       3
% 2.67/0.99  --prop_impl_unit_size                   0
% 2.67/0.99  --prop_impl_unit                        []
% 2.67/0.99  --share_sel_clauses                     true
% 2.67/0.99  --reset_solvers                         false
% 2.67/0.99  --bc_imp_inh                            [conj_cone]
% 2.67/0.99  --conj_cone_tolerance                   3.
% 2.67/0.99  --extra_neg_conj                        none
% 2.67/0.99  --large_theory_mode                     true
% 2.67/0.99  --prolific_symb_bound                   200
% 2.67/0.99  --lt_threshold                          2000
% 2.67/0.99  --clause_weak_htbl                      true
% 2.67/0.99  --gc_record_bc_elim                     false
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing Options
% 2.67/0.99  
% 2.67/0.99  --preprocessing_flag                    true
% 2.67/0.99  --time_out_prep_mult                    0.1
% 2.67/0.99  --splitting_mode                        input
% 2.67/0.99  --splitting_grd                         true
% 2.67/0.99  --splitting_cvd                         false
% 2.67/0.99  --splitting_cvd_svl                     false
% 2.67/0.99  --splitting_nvd                         32
% 2.67/0.99  --sub_typing                            true
% 2.67/0.99  --prep_gs_sim                           true
% 2.67/0.99  --prep_unflatten                        true
% 2.67/0.99  --prep_res_sim                          true
% 2.67/0.99  --prep_upred                            true
% 2.67/0.99  --prep_sem_filter                       exhaustive
% 2.67/0.99  --prep_sem_filter_out                   false
% 2.67/0.99  --pred_elim                             true
% 2.67/0.99  --res_sim_input                         true
% 2.67/0.99  --eq_ax_congr_red                       true
% 2.67/0.99  --pure_diseq_elim                       true
% 2.67/0.99  --brand_transform                       false
% 2.67/0.99  --non_eq_to_eq                          false
% 2.67/0.99  --prep_def_merge                        true
% 2.67/0.99  --prep_def_merge_prop_impl              false
% 2.67/0.99  --prep_def_merge_mbd                    true
% 2.67/0.99  --prep_def_merge_tr_red                 false
% 2.67/0.99  --prep_def_merge_tr_cl                  false
% 2.67/0.99  --smt_preprocessing                     true
% 2.67/0.99  --smt_ac_axioms                         fast
% 2.67/0.99  --preprocessed_out                      false
% 2.67/0.99  --preprocessed_stats                    false
% 2.67/0.99  
% 2.67/0.99  ------ Abstraction refinement Options
% 2.67/0.99  
% 2.67/0.99  --abstr_ref                             []
% 2.67/0.99  --abstr_ref_prep                        false
% 2.67/0.99  --abstr_ref_until_sat                   false
% 2.67/0.99  --abstr_ref_sig_restrict                funpre
% 2.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.99  --abstr_ref_under                       []
% 2.67/0.99  
% 2.67/0.99  ------ SAT Options
% 2.67/0.99  
% 2.67/0.99  --sat_mode                              false
% 2.67/0.99  --sat_fm_restart_options                ""
% 2.67/0.99  --sat_gr_def                            false
% 2.67/0.99  --sat_epr_types                         true
% 2.67/0.99  --sat_non_cyclic_types                  false
% 2.67/0.99  --sat_finite_models                     false
% 2.67/0.99  --sat_fm_lemmas                         false
% 2.67/0.99  --sat_fm_prep                           false
% 2.67/0.99  --sat_fm_uc_incr                        true
% 2.67/0.99  --sat_out_model                         small
% 2.67/0.99  --sat_out_clauses                       false
% 2.67/0.99  
% 2.67/0.99  ------ QBF Options
% 2.67/0.99  
% 2.67/0.99  --qbf_mode                              false
% 2.67/0.99  --qbf_elim_univ                         false
% 2.67/0.99  --qbf_dom_inst                          none
% 2.67/0.99  --qbf_dom_pre_inst                      false
% 2.67/0.99  --qbf_sk_in                             false
% 2.67/0.99  --qbf_pred_elim                         true
% 2.67/0.99  --qbf_split                             512
% 2.67/0.99  
% 2.67/0.99  ------ BMC1 Options
% 2.67/0.99  
% 2.67/0.99  --bmc1_incremental                      false
% 2.67/0.99  --bmc1_axioms                           reachable_all
% 2.67/0.99  --bmc1_min_bound                        0
% 2.67/0.99  --bmc1_max_bound                        -1
% 2.67/0.99  --bmc1_max_bound_default                -1
% 2.67/0.99  --bmc1_symbol_reachability              true
% 2.67/0.99  --bmc1_property_lemmas                  false
% 2.67/0.99  --bmc1_k_induction                      false
% 2.67/0.99  --bmc1_non_equiv_states                 false
% 2.67/0.99  --bmc1_deadlock                         false
% 2.67/0.99  --bmc1_ucm                              false
% 2.67/0.99  --bmc1_add_unsat_core                   none
% 2.67/0.99  --bmc1_unsat_core_children              false
% 2.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.99  --bmc1_out_stat                         full
% 2.67/0.99  --bmc1_ground_init                      false
% 2.67/0.99  --bmc1_pre_inst_next_state              false
% 2.67/0.99  --bmc1_pre_inst_state                   false
% 2.67/0.99  --bmc1_pre_inst_reach_state             false
% 2.67/0.99  --bmc1_out_unsat_core                   false
% 2.67/0.99  --bmc1_aig_witness_out                  false
% 2.67/0.99  --bmc1_verbose                          false
% 2.67/0.99  --bmc1_dump_clauses_tptp                false
% 2.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.99  --bmc1_dump_file                        -
% 2.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.99  --bmc1_ucm_extend_mode                  1
% 2.67/0.99  --bmc1_ucm_init_mode                    2
% 2.67/0.99  --bmc1_ucm_cone_mode                    none
% 2.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.99  --bmc1_ucm_relax_model                  4
% 2.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.99  --bmc1_ucm_layered_model                none
% 2.67/0.99  --bmc1_ucm_max_lemma_size               10
% 2.67/0.99  
% 2.67/0.99  ------ AIG Options
% 2.67/0.99  
% 2.67/0.99  --aig_mode                              false
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation Options
% 2.67/0.99  
% 2.67/0.99  --instantiation_flag                    true
% 2.67/0.99  --inst_sos_flag                         false
% 2.67/0.99  --inst_sos_phase                        true
% 2.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel_side                     num_symb
% 2.67/0.99  --inst_solver_per_active                1400
% 2.67/0.99  --inst_solver_calls_frac                1.
% 2.67/0.99  --inst_passive_queue_type               priority_queues
% 2.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.99  --inst_passive_queues_freq              [25;2]
% 2.67/0.99  --inst_dismatching                      true
% 2.67/0.99  --inst_eager_unprocessed_to_passive     true
% 2.67/0.99  --inst_prop_sim_given                   true
% 2.67/0.99  --inst_prop_sim_new                     false
% 2.67/0.99  --inst_subs_new                         false
% 2.67/0.99  --inst_eq_res_simp                      false
% 2.67/0.99  --inst_subs_given                       false
% 2.67/0.99  --inst_orphan_elimination               true
% 2.67/0.99  --inst_learning_loop_flag               true
% 2.67/0.99  --inst_learning_start                   3000
% 2.67/0.99  --inst_learning_factor                  2
% 2.67/0.99  --inst_start_prop_sim_after_learn       3
% 2.67/0.99  --inst_sel_renew                        solver
% 2.67/0.99  --inst_lit_activity_flag                true
% 2.67/0.99  --inst_restr_to_given                   false
% 2.67/0.99  --inst_activity_threshold               500
% 2.67/0.99  --inst_out_proof                        true
% 2.67/0.99  
% 2.67/0.99  ------ Resolution Options
% 2.67/0.99  
% 2.67/0.99  --resolution_flag                       true
% 2.67/0.99  --res_lit_sel                           adaptive
% 2.67/0.99  --res_lit_sel_side                      none
% 2.67/0.99  --res_ordering                          kbo
% 2.67/0.99  --res_to_prop_solver                    active
% 2.67/0.99  --res_prop_simpl_new                    false
% 2.67/0.99  --res_prop_simpl_given                  true
% 2.67/0.99  --res_passive_queue_type                priority_queues
% 2.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.99  --res_passive_queues_freq               [15;5]
% 2.67/0.99  --res_forward_subs                      full
% 2.67/0.99  --res_backward_subs                     full
% 2.67/0.99  --res_forward_subs_resolution           true
% 2.67/0.99  --res_backward_subs_resolution          true
% 2.67/0.99  --res_orphan_elimination                true
% 2.67/0.99  --res_time_limit                        2.
% 2.67/0.99  --res_out_proof                         true
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Options
% 2.67/0.99  
% 2.67/0.99  --superposition_flag                    true
% 2.67/0.99  --sup_passive_queue_type                priority_queues
% 2.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.99  --demod_completeness_check              fast
% 2.67/0.99  --demod_use_ground                      true
% 2.67/0.99  --sup_to_prop_solver                    passive
% 2.67/0.99  --sup_prop_simpl_new                    true
% 2.67/0.99  --sup_prop_simpl_given                  true
% 2.67/0.99  --sup_fun_splitting                     false
% 2.67/0.99  --sup_smt_interval                      50000
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Simplification Setup
% 2.67/0.99  
% 2.67/0.99  --sup_indices_passive                   []
% 2.67/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_full_bw                           [BwDemod]
% 2.67/0.99  --sup_immed_triv                        [TrivRules]
% 2.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_immed_bw_main                     []
% 2.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  
% 2.67/0.99  ------ Combination Options
% 2.67/0.99  
% 2.67/0.99  --comb_res_mult                         3
% 2.67/0.99  --comb_sup_mult                         2
% 2.67/0.99  --comb_inst_mult                        10
% 2.67/0.99  
% 2.67/0.99  ------ Debug Options
% 2.67/0.99  
% 2.67/0.99  --dbg_backtrace                         false
% 2.67/0.99  --dbg_dump_prop_clauses                 false
% 2.67/0.99  --dbg_dump_prop_clauses_file            -
% 2.67/0.99  --dbg_out_stat                          false
% 2.67/0.99  ------ Parsing...
% 2.67/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.99  ------ Proving...
% 2.67/0.99  ------ Problem Properties 
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  clauses                                 32
% 2.67/0.99  conjectures                             3
% 2.67/0.99  EPR                                     3
% 2.67/0.99  Horn                                    28
% 2.67/0.99  unary                                   8
% 2.67/0.99  binary                                  6
% 2.67/0.99  lits                                    90
% 2.67/0.99  lits eq                                 42
% 2.67/0.99  fd_pure                                 0
% 2.67/0.99  fd_pseudo                               0
% 2.67/0.99  fd_cond                                 3
% 2.67/0.99  fd_pseudo_cond                          0
% 2.67/0.99  AC symbols                              0
% 2.67/0.99  
% 2.67/0.99  ------ Schedule dynamic 5 is on 
% 2.67/0.99  
% 2.67/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  ------ 
% 2.67/0.99  Current options:
% 2.67/0.99  ------ 
% 2.67/0.99  
% 2.67/0.99  ------ Input Options
% 2.67/0.99  
% 2.67/0.99  --out_options                           all
% 2.67/0.99  --tptp_safe_out                         true
% 2.67/0.99  --problem_path                          ""
% 2.67/0.99  --include_path                          ""
% 2.67/0.99  --clausifier                            res/vclausify_rel
% 2.67/0.99  --clausifier_options                    --mode clausify
% 2.67/0.99  --stdin                                 false
% 2.67/0.99  --stats_out                             all
% 2.67/0.99  
% 2.67/0.99  ------ General Options
% 2.67/0.99  
% 2.67/0.99  --fof                                   false
% 2.67/0.99  --time_out_real                         305.
% 2.67/0.99  --time_out_virtual                      -1.
% 2.67/0.99  --symbol_type_check                     false
% 2.67/0.99  --clausify_out                          false
% 2.67/0.99  --sig_cnt_out                           false
% 2.67/0.99  --trig_cnt_out                          false
% 2.67/0.99  --trig_cnt_out_tolerance                1.
% 2.67/0.99  --trig_cnt_out_sk_spl                   false
% 2.67/0.99  --abstr_cl_out                          false
% 2.67/0.99  
% 2.67/0.99  ------ Global Options
% 2.67/0.99  
% 2.67/0.99  --schedule                              default
% 2.67/0.99  --add_important_lit                     false
% 2.67/0.99  --prop_solver_per_cl                    1000
% 2.67/0.99  --min_unsat_core                        false
% 2.67/0.99  --soft_assumptions                      false
% 2.67/0.99  --soft_lemma_size                       3
% 2.67/0.99  --prop_impl_unit_size                   0
% 2.67/0.99  --prop_impl_unit                        []
% 2.67/0.99  --share_sel_clauses                     true
% 2.67/0.99  --reset_solvers                         false
% 2.67/0.99  --bc_imp_inh                            [conj_cone]
% 2.67/0.99  --conj_cone_tolerance                   3.
% 2.67/0.99  --extra_neg_conj                        none
% 2.67/0.99  --large_theory_mode                     true
% 2.67/0.99  --prolific_symb_bound                   200
% 2.67/0.99  --lt_threshold                          2000
% 2.67/0.99  --clause_weak_htbl                      true
% 2.67/0.99  --gc_record_bc_elim                     false
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing Options
% 2.67/0.99  
% 2.67/0.99  --preprocessing_flag                    true
% 2.67/0.99  --time_out_prep_mult                    0.1
% 2.67/0.99  --splitting_mode                        input
% 2.67/0.99  --splitting_grd                         true
% 2.67/0.99  --splitting_cvd                         false
% 2.67/0.99  --splitting_cvd_svl                     false
% 2.67/0.99  --splitting_nvd                         32
% 2.67/0.99  --sub_typing                            true
% 2.67/0.99  --prep_gs_sim                           true
% 2.67/0.99  --prep_unflatten                        true
% 2.67/0.99  --prep_res_sim                          true
% 2.67/0.99  --prep_upred                            true
% 2.67/0.99  --prep_sem_filter                       exhaustive
% 2.67/0.99  --prep_sem_filter_out                   false
% 2.67/0.99  --pred_elim                             true
% 2.67/0.99  --res_sim_input                         true
% 2.67/0.99  --eq_ax_congr_red                       true
% 2.67/0.99  --pure_diseq_elim                       true
% 2.67/0.99  --brand_transform                       false
% 2.67/0.99  --non_eq_to_eq                          false
% 2.67/0.99  --prep_def_merge                        true
% 2.67/0.99  --prep_def_merge_prop_impl              false
% 2.67/0.99  --prep_def_merge_mbd                    true
% 2.67/0.99  --prep_def_merge_tr_red                 false
% 2.67/0.99  --prep_def_merge_tr_cl                  false
% 2.67/0.99  --smt_preprocessing                     true
% 2.67/0.99  --smt_ac_axioms                         fast
% 2.67/0.99  --preprocessed_out                      false
% 2.67/0.99  --preprocessed_stats                    false
% 2.67/0.99  
% 2.67/0.99  ------ Abstraction refinement Options
% 2.67/0.99  
% 2.67/0.99  --abstr_ref                             []
% 2.67/0.99  --abstr_ref_prep                        false
% 2.67/0.99  --abstr_ref_until_sat                   false
% 2.67/0.99  --abstr_ref_sig_restrict                funpre
% 2.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.99  --abstr_ref_under                       []
% 2.67/0.99  
% 2.67/0.99  ------ SAT Options
% 2.67/0.99  
% 2.67/0.99  --sat_mode                              false
% 2.67/0.99  --sat_fm_restart_options                ""
% 2.67/0.99  --sat_gr_def                            false
% 2.67/0.99  --sat_epr_types                         true
% 2.67/0.99  --sat_non_cyclic_types                  false
% 2.67/0.99  --sat_finite_models                     false
% 2.67/0.99  --sat_fm_lemmas                         false
% 2.67/0.99  --sat_fm_prep                           false
% 2.67/0.99  --sat_fm_uc_incr                        true
% 2.67/0.99  --sat_out_model                         small
% 2.67/0.99  --sat_out_clauses                       false
% 2.67/0.99  
% 2.67/0.99  ------ QBF Options
% 2.67/0.99  
% 2.67/0.99  --qbf_mode                              false
% 2.67/0.99  --qbf_elim_univ                         false
% 2.67/0.99  --qbf_dom_inst                          none
% 2.67/0.99  --qbf_dom_pre_inst                      false
% 2.67/0.99  --qbf_sk_in                             false
% 2.67/0.99  --qbf_pred_elim                         true
% 2.67/0.99  --qbf_split                             512
% 2.67/0.99  
% 2.67/0.99  ------ BMC1 Options
% 2.67/0.99  
% 2.67/0.99  --bmc1_incremental                      false
% 2.67/0.99  --bmc1_axioms                           reachable_all
% 2.67/0.99  --bmc1_min_bound                        0
% 2.67/0.99  --bmc1_max_bound                        -1
% 2.67/0.99  --bmc1_max_bound_default                -1
% 2.67/0.99  --bmc1_symbol_reachability              true
% 2.67/0.99  --bmc1_property_lemmas                  false
% 2.67/0.99  --bmc1_k_induction                      false
% 2.67/0.99  --bmc1_non_equiv_states                 false
% 2.67/0.99  --bmc1_deadlock                         false
% 2.67/0.99  --bmc1_ucm                              false
% 2.67/0.99  --bmc1_add_unsat_core                   none
% 2.67/0.99  --bmc1_unsat_core_children              false
% 2.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.99  --bmc1_out_stat                         full
% 2.67/0.99  --bmc1_ground_init                      false
% 2.67/0.99  --bmc1_pre_inst_next_state              false
% 2.67/0.99  --bmc1_pre_inst_state                   false
% 2.67/0.99  --bmc1_pre_inst_reach_state             false
% 2.67/0.99  --bmc1_out_unsat_core                   false
% 2.67/0.99  --bmc1_aig_witness_out                  false
% 2.67/0.99  --bmc1_verbose                          false
% 2.67/0.99  --bmc1_dump_clauses_tptp                false
% 2.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.99  --bmc1_dump_file                        -
% 2.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.99  --bmc1_ucm_extend_mode                  1
% 2.67/0.99  --bmc1_ucm_init_mode                    2
% 2.67/0.99  --bmc1_ucm_cone_mode                    none
% 2.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.99  --bmc1_ucm_relax_model                  4
% 2.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.99  --bmc1_ucm_layered_model                none
% 2.67/0.99  --bmc1_ucm_max_lemma_size               10
% 2.67/0.99  
% 2.67/0.99  ------ AIG Options
% 2.67/0.99  
% 2.67/0.99  --aig_mode                              false
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation Options
% 2.67/0.99  
% 2.67/0.99  --instantiation_flag                    true
% 2.67/0.99  --inst_sos_flag                         false
% 2.67/0.99  --inst_sos_phase                        true
% 2.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel_side                     none
% 2.67/0.99  --inst_solver_per_active                1400
% 2.67/0.99  --inst_solver_calls_frac                1.
% 2.67/0.99  --inst_passive_queue_type               priority_queues
% 2.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.99  --inst_passive_queues_freq              [25;2]
% 2.67/0.99  --inst_dismatching                      true
% 2.67/0.99  --inst_eager_unprocessed_to_passive     true
% 2.67/0.99  --inst_prop_sim_given                   true
% 2.67/0.99  --inst_prop_sim_new                     false
% 2.67/0.99  --inst_subs_new                         false
% 2.67/0.99  --inst_eq_res_simp                      false
% 2.67/0.99  --inst_subs_given                       false
% 2.67/0.99  --inst_orphan_elimination               true
% 2.67/0.99  --inst_learning_loop_flag               true
% 2.67/0.99  --inst_learning_start                   3000
% 2.67/0.99  --inst_learning_factor                  2
% 2.67/0.99  --inst_start_prop_sim_after_learn       3
% 2.67/0.99  --inst_sel_renew                        solver
% 2.67/0.99  --inst_lit_activity_flag                true
% 2.67/0.99  --inst_restr_to_given                   false
% 2.67/0.99  --inst_activity_threshold               500
% 2.67/0.99  --inst_out_proof                        true
% 2.67/0.99  
% 2.67/0.99  ------ Resolution Options
% 2.67/0.99  
% 2.67/0.99  --resolution_flag                       false
% 2.67/0.99  --res_lit_sel                           adaptive
% 2.67/0.99  --res_lit_sel_side                      none
% 2.67/0.99  --res_ordering                          kbo
% 2.67/0.99  --res_to_prop_solver                    active
% 2.67/0.99  --res_prop_simpl_new                    false
% 2.67/0.99  --res_prop_simpl_given                  true
% 2.67/0.99  --res_passive_queue_type                priority_queues
% 2.67/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.99  --res_passive_queues_freq               [15;5]
% 2.67/0.99  --res_forward_subs                      full
% 2.67/0.99  --res_backward_subs                     full
% 2.67/0.99  --res_forward_subs_resolution           true
% 2.67/0.99  --res_backward_subs_resolution          true
% 2.67/0.99  --res_orphan_elimination                true
% 2.67/0.99  --res_time_limit                        2.
% 2.67/0.99  --res_out_proof                         true
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Options
% 2.67/0.99  
% 2.67/0.99  --superposition_flag                    true
% 2.67/0.99  --sup_passive_queue_type                priority_queues
% 2.67/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.99  --demod_completeness_check              fast
% 2.67/0.99  --demod_use_ground                      true
% 2.67/0.99  --sup_to_prop_solver                    passive
% 2.67/0.99  --sup_prop_simpl_new                    true
% 2.67/0.99  --sup_prop_simpl_given                  true
% 2.67/0.99  --sup_fun_splitting                     false
% 2.67/0.99  --sup_smt_interval                      50000
% 2.67/0.99  
% 2.67/0.99  ------ Superposition Simplification Setup
% 2.67/0.99  
% 2.67/0.99  --sup_indices_passive                   []
% 2.67/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_full_bw                           [BwDemod]
% 2.67/0.99  --sup_immed_triv                        [TrivRules]
% 2.67/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_immed_bw_main                     []
% 2.67/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.99  
% 2.67/0.99  ------ Combination Options
% 2.67/0.99  
% 2.67/0.99  --comb_res_mult                         3
% 2.67/0.99  --comb_sup_mult                         2
% 2.67/0.99  --comb_inst_mult                        10
% 2.67/0.99  
% 2.67/0.99  ------ Debug Options
% 2.67/0.99  
% 2.67/0.99  --dbg_backtrace                         false
% 2.67/0.99  --dbg_dump_prop_clauses                 false
% 2.67/0.99  --dbg_dump_prop_clauses_file            -
% 2.67/0.99  --dbg_out_stat                          false
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  ------ Proving...
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS status Theorem for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99   Resolution empty clause
% 2.67/0.99  
% 2.67/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  fof(f12,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f29,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f12])).
% 2.67/0.99  
% 2.67/0.99  fof(f30,plain,(
% 2.67/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(flattening,[],[f29])).
% 2.67/0.99  
% 2.67/0.99  fof(f38,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(nnf_transformation,[],[f30])).
% 2.67/0.99  
% 2.67/0.99  fof(f56,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f38])).
% 2.67/0.99  
% 2.67/0.99  fof(f15,conjecture,(
% 2.67/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f16,negated_conjecture,(
% 2.67/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.67/0.99    inference(negated_conjecture,[],[f15])).
% 2.67/0.99  
% 2.67/0.99  fof(f35,plain,(
% 2.67/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.67/0.99    inference(ennf_transformation,[],[f16])).
% 2.67/0.99  
% 2.67/0.99  fof(f36,plain,(
% 2.67/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.67/0.99    inference(flattening,[],[f35])).
% 2.67/0.99  
% 2.67/0.99  fof(f39,plain,(
% 2.67/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.67/0.99    introduced(choice_axiom,[])).
% 2.67/0.99  
% 2.67/0.99  fof(f40,plain,(
% 2.67/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39])).
% 2.67/0.99  
% 2.67/0.99  fof(f69,plain,(
% 2.67/0.99    v1_funct_2(sK2,sK0,sK1)),
% 2.67/0.99    inference(cnf_transformation,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f70,plain,(
% 2.67/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.67/0.99    inference(cnf_transformation,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f10,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f27,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f10])).
% 2.67/0.99  
% 2.67/0.99  fof(f54,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f27])).
% 2.67/0.99  
% 2.67/0.99  fof(f9,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f26,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f9])).
% 2.67/0.99  
% 2.67/0.99  fof(f53,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f26])).
% 2.67/0.99  
% 2.67/0.99  fof(f7,axiom,(
% 2.67/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f24,plain,(
% 2.67/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f7])).
% 2.67/0.99  
% 2.67/0.99  fof(f25,plain,(
% 2.67/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/0.99    inference(flattening,[],[f24])).
% 2.67/0.99  
% 2.67/0.99  fof(f50,plain,(
% 2.67/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f25])).
% 2.67/0.99  
% 2.67/0.99  fof(f71,plain,(
% 2.67/0.99    v2_funct_1(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f68,plain,(
% 2.67/0.99    v1_funct_1(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f13,axiom,(
% 2.67/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f31,plain,(
% 2.67/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f13])).
% 2.67/0.99  
% 2.67/0.99  fof(f32,plain,(
% 2.67/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/0.99    inference(flattening,[],[f31])).
% 2.67/0.99  
% 2.67/0.99  fof(f64,plain,(
% 2.67/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f32])).
% 2.67/0.99  
% 2.67/0.99  fof(f49,plain,(
% 2.67/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f25])).
% 2.67/0.99  
% 2.67/0.99  fof(f11,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f28,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f11])).
% 2.67/0.99  
% 2.67/0.99  fof(f55,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f28])).
% 2.67/0.99  
% 2.67/0.99  fof(f72,plain,(
% 2.67/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.67/0.99    inference(cnf_transformation,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f6,axiom,(
% 2.67/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f22,plain,(
% 2.67/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f6])).
% 2.67/0.99  
% 2.67/0.99  fof(f23,plain,(
% 2.67/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/0.99    inference(flattening,[],[f22])).
% 2.67/0.99  
% 2.67/0.99  fof(f48,plain,(
% 2.67/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f23])).
% 2.67/0.99  
% 2.67/0.99  fof(f47,plain,(
% 2.67/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f23])).
% 2.67/0.99  
% 2.67/0.99  fof(f5,axiom,(
% 2.67/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f20,plain,(
% 2.67/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.67/0.99    inference(ennf_transformation,[],[f5])).
% 2.67/0.99  
% 2.67/0.99  fof(f21,plain,(
% 2.67/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.67/0.99    inference(flattening,[],[f20])).
% 2.67/0.99  
% 2.67/0.99  fof(f46,plain,(
% 2.67/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f21])).
% 2.67/0.99  
% 2.67/0.99  fof(f63,plain,(
% 2.67/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f32])).
% 2.67/0.99  
% 2.67/0.99  fof(f73,plain,(
% 2.67/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.67/0.99    inference(cnf_transformation,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f8,axiom,(
% 2.67/0.99    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f17,plain,(
% 2.67/0.99    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.67/0.99    inference(pure_predicate_removal,[],[f8])).
% 2.67/0.99  
% 2.67/0.99  fof(f18,plain,(
% 2.67/0.99    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 2.67/0.99    inference(pure_predicate_removal,[],[f17])).
% 2.67/0.99  
% 2.67/0.99  fof(f37,plain,(
% 2.67/0.99    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 2.67/0.99    inference(rectify,[],[f18])).
% 2.67/0.99  
% 2.67/0.99  fof(f51,plain,(
% 2.67/0.99    v1_relat_1(k1_xboole_0)),
% 2.67/0.99    inference(cnf_transformation,[],[f37])).
% 2.67/0.99  
% 2.67/0.99  fof(f45,plain,(
% 2.67/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f21])).
% 2.67/0.99  
% 2.67/0.99  fof(f4,axiom,(
% 2.67/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f43,plain,(
% 2.67/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.67/0.99    inference(cnf_transformation,[],[f4])).
% 2.67/0.99  
% 2.67/0.99  fof(f1,axiom,(
% 2.67/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f41,plain,(
% 2.67/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f1])).
% 2.67/0.99  
% 2.67/0.99  fof(f14,axiom,(
% 2.67/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f33,plain,(
% 2.67/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.67/0.99    inference(ennf_transformation,[],[f14])).
% 2.67/0.99  
% 2.67/0.99  fof(f34,plain,(
% 2.67/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.67/0.99    inference(flattening,[],[f33])).
% 2.67/0.99  
% 2.67/0.99  fof(f66,plain,(
% 2.67/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f34])).
% 2.67/0.99  
% 2.67/0.99  fof(f52,plain,(
% 2.67/0.99    v1_funct_1(k1_xboole_0)),
% 2.67/0.99    inference(cnf_transformation,[],[f37])).
% 2.67/0.99  
% 2.67/0.99  fof(f2,axiom,(
% 2.67/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.67/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f42,plain,(
% 2.67/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f2])).
% 2.67/0.99  
% 2.67/0.99  cnf(c_20,plain,
% 2.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.67/0.99      | k1_xboole_0 = X2 ),
% 2.67/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_31,negated_conjecture,
% 2.67/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_610,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.67/0.99      | sK0 != X1
% 2.67/0.99      | sK1 != X2
% 2.67/0.99      | sK2 != X0
% 2.67/0.99      | k1_xboole_0 = X2 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_611,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.67/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.67/0.99      | k1_xboole_0 = sK1 ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_610]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_30,negated_conjecture,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.67/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_613,plain,
% 2.67/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.67/0.99      inference(global_propositional_subsumption,[status(thm)],[c_611,c_30]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1407,plain,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_13,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1410,plain,
% 2.67/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2836,plain,
% 2.67/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1407,c_1410]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2929,plain,
% 2.67/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_613,c_2836]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_12,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1411,plain,
% 2.67/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.67/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2051,plain,
% 2.67/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1407,c_1411]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_8,plain,
% 2.67/0.99      ( ~ v2_funct_1(X0)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_29,negated_conjecture,
% 2.67/0.99      ( v2_funct_1(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_384,plain,
% 2.67/0.99      ( ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.67/0.99      | sK2 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_385,plain,
% 2.67/0.99      ( ~ v1_funct_1(sK2)
% 2.67/0.99      | ~ v1_relat_1(sK2)
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_384]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_32,negated_conjecture,
% 2.67/0.99      ( v1_funct_1(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_387,plain,
% 2.67/0.99      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/0.99      inference(global_propositional_subsumption,[status(thm)],[c_385,c_32]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1403,plain,
% 2.67/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2131,plain,
% 2.67/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2051,c_1403]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_21,plain,
% 2.67/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1408,plain,
% 2.67/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.67/0.99      | v1_funct_1(X0) != iProver_top
% 2.67/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3561,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2131,c_1408]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_9,plain,
% 2.67/0.99      ( ~ v2_funct_1(X0)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_370,plain,
% 2.67/0.99      ( ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.67/0.99      | sK2 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_371,plain,
% 2.67/0.99      ( ~ v1_funct_1(sK2)
% 2.67/0.99      | ~ v1_relat_1(sK2)
% 2.67/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_370]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_373,plain,
% 2.67/0.99      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/0.99      inference(global_propositional_subsumption,[status(thm)],[c_371,c_32]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1404,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2130,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2051,c_1404]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_14,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1409,plain,
% 2.67/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2282,plain,
% 2.67/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1407,c_1409]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_28,negated_conjecture,
% 2.67/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.67/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2284,plain,
% 2.67/0.99      ( k2_relat_1(sK2) = sK1 ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_2282,c_28]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2448,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_2130,c_2284]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3574,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_3561,c_2448]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_33,plain,
% 2.67/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_35,plain,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_6,plain,
% 2.67/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1665,plain,
% 2.67/0.99      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1666,plain,
% 2.67/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1665]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1668,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1800,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.67/0.99      | v1_relat_1(sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1668]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1801,plain,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.67/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3725,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_3574,c_33,c_35,c_1666,c_1801]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3731,plain,
% 2.67/0.99      ( sK1 = k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2929,c_3725]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_7,plain,
% 2.67/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1414,plain,
% 2.67/0.99      ( v1_funct_1(X0) != iProver_top
% 2.67/0.99      | v1_relat_1(X0) != iProver_top
% 2.67/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4,plain,
% 2.67/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1417,plain,
% 2.67/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 2.67/0.99      | k1_xboole_0 = X0
% 2.67/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2467,plain,
% 2.67/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 2.67/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2131,c_1417]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3303,plain,
% 2.67/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 2.67/0.99      | sK0 != k1_xboole_0
% 2.67/0.99      | sK1 = k1_xboole_0
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2929,c_2467]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_22,plain,
% 2.67/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_27,negated_conjecture,
% 2.67/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.67/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_621,plain,
% 2.67/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | k2_funct_1(sK2) != X0
% 2.67/0.99      | k1_relat_1(X0) != sK1
% 2.67/0.99      | k2_relat_1(X0) != sK0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_622,plain,
% 2.67/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.67/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_621]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_634,plain,
% 2.67/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.67/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_622,c_12]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1393,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_639,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1958,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_1393,c_33,c_35,c_639,c_1666,c_1801]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1959,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(renaming,[status(thm)],[c_1958]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2450,plain,
% 2.67/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/0.99      | sK1 != sK1
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2448,c_1959]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2457,plain,
% 2.67/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(equality_resolution_simp,[status(thm)],[c_2450]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3291,plain,
% 2.67/0.99      ( k1_relat_1(sK2) != sK0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_2457,c_2131]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_11,plain,
% 2.67/0.99      ( v1_relat_1(k1_xboole_0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5,plain,
% 2.67/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_94,plain,
% 2.67/0.99      ( ~ v1_relat_1(k1_xboole_0)
% 2.67/0.99      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.67/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3,plain,
% 2.67/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_927,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1887,plain,
% 2.67/0.99      ( k1_relat_1(sK2) != X0
% 2.67/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.67/0.99      | k1_xboole_0 != X0 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_927]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2201,plain,
% 2.67/0.99      ( k1_relat_1(sK2) != k1_relat_1(X0)
% 2.67/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.67/0.99      | k1_xboole_0 != k1_relat_1(X0) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1887]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2203,plain,
% 2.67/0.99      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 2.67/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.67/0.99      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_2201]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_931,plain,
% 2.67/0.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.67/0.99      theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2202,plain,
% 2.67/0.99      ( k1_relat_1(sK2) = k1_relat_1(X0) | sK2 != X0 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_931]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2204,plain,
% 2.67/0.99      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_2202]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2291,plain,
% 2.67/0.99      ( sK1 != k1_xboole_0
% 2.67/0.99      | sK2 = k1_xboole_0
% 2.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2284,c_1417]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_0,plain,
% 2.67/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_25,plain,
% 2.67/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.67/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_324,plain,
% 2.67/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | X1 != X2
% 2.67/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_325,plain,
% 2.67/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_640,plain,
% 2.67/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | ~ v1_relat_1(X0)
% 2.67/0.99      | k2_funct_1(sK2) != X0
% 2.67/0.99      | k1_relat_1(X0) != sK1
% 2.67/0.99      | k2_relat_1(X0) != k1_xboole_0
% 2.67/0.99      | sK0 != X1 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_325,c_27]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_641,plain,
% 2.67/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.67/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_640]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_653,plain,
% 2.67/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.67/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_641,c_12]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1392,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_658,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1804,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.67/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_1392,c_33,c_35,c_658,c_1666,c_1801]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1805,plain,
% 2.67/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(renaming,[status(thm)],[c_1804]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2451,plain,
% 2.67/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.67/0.99      | sK1 != sK1
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2448,c_1805]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2452,plain,
% 2.67/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(equality_resolution_simp,[status(thm)],[c_2451]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2639,plain,
% 2.67/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_2452,c_2131]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2858,plain,
% 2.67/0.99      ( k1_relat_1(X0) != X1
% 2.67/0.99      | k1_xboole_0 != X1
% 2.67/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_927]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2859,plain,
% 2.67/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.67/0.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.67/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_2858]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3295,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_3291,c_35,c_11,c_94,c_3,c_1801,c_2203,c_2204,c_2291,
% 2.67/0.99                 c_2639,c_2859,c_2929]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3987,plain,
% 2.67/0.99      ( sK1 = k1_xboole_0 | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_3303,c_35,c_11,c_94,c_3,c_1801,c_2203,c_2204,c_2291,
% 2.67/0.99                 c_2639,c_2859,c_2929,c_3291,c_3731]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3993,plain,
% 2.67/0.99      ( sK1 = k1_xboole_0
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1414,c_3987]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3996,plain,
% 2.67/0.99      ( sK1 = k1_xboole_0 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_3731,c_33,c_35,c_1801,c_3993]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4010,plain,
% 2.67/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_3996,c_2639]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2307,plain,
% 2.67/0.99      ( ~ v1_relat_1(sK2) | sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.67/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2291]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2399,plain,
% 2.67/0.99      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2291,c_30,c_1800,c_2307]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2400,plain,
% 2.67/0.99      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.67/0.99      inference(renaming,[status(thm)],[c_2399]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4015,plain,
% 2.67/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_3996,c_2400]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4064,plain,
% 2.67/0.99      ( sK2 = k1_xboole_0 ),
% 2.67/0.99      inference(equality_resolution_simp,[status(thm)],[c_4015]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4108,plain,
% 2.67/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_4010,c_4064]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4111,plain,
% 2.67/0.99      ( k1_xboole_0 != k1_xboole_0
% 2.67/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_4108,c_3]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4112,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/0.99      inference(equality_resolution_simp,[status(thm)],[c_4111]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1416,plain,
% 2.67/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 2.67/0.99      | k1_xboole_0 = X0
% 2.67/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2464,plain,
% 2.67/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 2.67/0.99      | sK1 != k1_xboole_0
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_2448,c_1416]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4012,plain,
% 2.67/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 2.67/0.99      | k1_xboole_0 != k1_xboole_0
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_3996,c_2464]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4094,plain,
% 2.67/0.99      ( k2_funct_1(sK2) = k1_xboole_0
% 2.67/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(equality_resolution_simp,[status(thm)],[c_4012]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4095,plain,
% 2.67/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 2.67/0.99      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_4094,c_4064]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_79,plain,
% 2.67/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_10,plain,
% 2.67/0.99      ( v1_funct_1(k1_xboole_0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_80,plain,
% 2.67/0.99      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_87,plain,
% 2.67/0.99      ( v1_funct_1(X0) != iProver_top
% 2.67/0.99      | v1_relat_1(X0) != iProver_top
% 2.67/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_89,plain,
% 2.67/0.99      ( v1_funct_1(k1_xboole_0) != iProver_top
% 2.67/0.99      | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.67/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_87]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4733,plain,
% 2.67/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_4095,c_79,c_80,c_89]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5067,plain,
% 2.67/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_4112,c_4733]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1,plain,
% 2.67/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1418,plain,
% 2.67/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5069,plain,
% 2.67/0.99      ( $false ),
% 2.67/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5067,c_1418]) ).
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  ------                               Statistics
% 2.67/0.99  
% 2.67/0.99  ------ General
% 2.67/0.99  
% 2.67/0.99  abstr_ref_over_cycles:                  0
% 2.67/0.99  abstr_ref_under_cycles:                 0
% 2.67/0.99  gc_basic_clause_elim:                   0
% 2.67/0.99  forced_gc_time:                         0
% 2.67/0.99  parsing_time:                           0.009
% 2.67/0.99  unif_index_cands_time:                  0.
% 2.67/0.99  unif_index_add_time:                    0.
% 2.67/0.99  orderings_time:                         0.
% 2.67/0.99  out_proof_time:                         0.01
% 2.67/0.99  total_time:                             0.169
% 2.67/0.99  num_of_symbols:                         48
% 2.67/0.99  num_of_terms:                           3341
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing
% 2.67/0.99  
% 2.67/0.99  num_of_splits:                          0
% 2.67/0.99  num_of_split_atoms:                     0
% 2.67/0.99  num_of_reused_defs:                     0
% 2.67/0.99  num_eq_ax_congr_red:                    3
% 2.67/0.99  num_of_sem_filtered_clauses:            1
% 2.67/0.99  num_of_subtypes:                        0
% 2.67/0.99  monotx_restored_types:                  0
% 2.67/0.99  sat_num_of_epr_types:                   0
% 2.67/0.99  sat_num_of_non_cyclic_types:            0
% 2.67/0.99  sat_guarded_non_collapsed_types:        0
% 2.67/0.99  num_pure_diseq_elim:                    0
% 2.67/0.99  simp_replaced_by:                       0
% 2.67/0.99  res_preprocessed:                       152
% 2.67/0.99  prep_upred:                             0
% 2.67/0.99  prep_unflattend:                        55
% 2.67/0.99  smt_new_axioms:                         0
% 2.67/0.99  pred_elim_cands:                        3
% 2.67/0.99  pred_elim:                              3
% 2.67/0.99  pred_elim_cl:                           -1
% 2.67/0.99  pred_elim_cycles:                       5
% 2.67/0.99  merged_defs:                            0
% 2.67/0.99  merged_defs_ncl:                        0
% 2.67/0.99  bin_hyper_res:                          0
% 2.67/0.99  prep_cycles:                            4
% 2.67/0.99  pred_elim_time:                         0.009
% 2.67/0.99  splitting_time:                         0.
% 2.67/0.99  sem_filter_time:                        0.
% 2.67/0.99  monotx_time:                            0.
% 2.67/0.99  subtype_inf_time:                       0.
% 2.67/0.99  
% 2.67/0.99  ------ Problem properties
% 2.67/0.99  
% 2.67/0.99  clauses:                                32
% 2.67/0.99  conjectures:                            3
% 2.67/0.99  epr:                                    3
% 2.67/0.99  horn:                                   28
% 2.67/0.99  ground:                                 18
% 2.67/0.99  unary:                                  8
% 2.67/0.99  binary:                                 6
% 2.67/0.99  lits:                                   90
% 2.67/0.99  lits_eq:                                42
% 2.67/0.99  fd_pure:                                0
% 2.67/0.99  fd_pseudo:                              0
% 2.67/0.99  fd_cond:                                3
% 2.67/0.99  fd_pseudo_cond:                         0
% 2.67/0.99  ac_symbols:                             0
% 2.67/0.99  
% 2.67/0.99  ------ Propositional Solver
% 2.67/0.99  
% 2.67/0.99  prop_solver_calls:                      28
% 2.67/0.99  prop_fast_solver_calls:                 1159
% 2.67/0.99  smt_solver_calls:                       0
% 2.67/0.99  smt_fast_solver_calls:                  0
% 2.67/0.99  prop_num_of_clauses:                    1548
% 2.67/0.99  prop_preprocess_simplified:             5177
% 2.67/0.99  prop_fo_subsumed:                       40
% 2.67/0.99  prop_solver_time:                       0.
% 2.67/0.99  smt_solver_time:                        0.
% 2.67/0.99  smt_fast_solver_time:                   0.
% 2.67/0.99  prop_fast_solver_time:                  0.
% 2.67/0.99  prop_unsat_core_time:                   0.
% 2.67/0.99  
% 2.67/0.99  ------ QBF
% 2.67/0.99  
% 2.67/0.99  qbf_q_res:                              0
% 2.67/0.99  qbf_num_tautologies:                    0
% 2.67/0.99  qbf_prep_cycles:                        0
% 2.67/0.99  
% 2.67/0.99  ------ BMC1
% 2.67/0.99  
% 2.67/0.99  bmc1_current_bound:                     -1
% 2.67/0.99  bmc1_last_solved_bound:                 -1
% 2.67/0.99  bmc1_unsat_core_size:                   -1
% 2.67/0.99  bmc1_unsat_core_parents_size:           -1
% 2.67/0.99  bmc1_merge_next_fun:                    0
% 2.67/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation
% 2.67/0.99  
% 2.67/0.99  inst_num_of_clauses:                    545
% 2.67/0.99  inst_num_in_passive:                    101
% 2.67/0.99  inst_num_in_active:                     286
% 2.67/0.99  inst_num_in_unprocessed:                158
% 2.67/0.99  inst_num_of_loops:                      350
% 2.67/0.99  inst_num_of_learning_restarts:          0
% 2.67/0.99  inst_num_moves_active_passive:          61
% 2.67/0.99  inst_lit_activity:                      0
% 2.67/0.99  inst_lit_activity_moves:                0
% 2.67/0.99  inst_num_tautologies:                   0
% 2.67/0.99  inst_num_prop_implied:                  0
% 2.67/0.99  inst_num_existing_simplified:           0
% 2.67/0.99  inst_num_eq_res_simplified:             0
% 2.67/0.99  inst_num_child_elim:                    0
% 2.67/0.99  inst_num_of_dismatching_blockings:      272
% 2.67/0.99  inst_num_of_non_proper_insts:           512
% 2.67/0.99  inst_num_of_duplicates:                 0
% 2.67/0.99  inst_inst_num_from_inst_to_res:         0
% 2.67/0.99  inst_dismatching_checking_time:         0.
% 2.67/0.99  
% 2.67/0.99  ------ Resolution
% 2.67/0.99  
% 2.67/0.99  res_num_of_clauses:                     0
% 2.67/0.99  res_num_in_passive:                     0
% 2.67/0.99  res_num_in_active:                      0
% 2.67/0.99  res_num_of_loops:                       156
% 2.67/0.99  res_forward_subset_subsumed:            38
% 2.67/0.99  res_backward_subset_subsumed:           2
% 2.67/0.99  res_forward_subsumed:                   0
% 2.67/0.99  res_backward_subsumed:                  0
% 2.67/0.99  res_forward_subsumption_resolution:     5
% 2.67/0.99  res_backward_subsumption_resolution:    0
% 2.67/0.99  res_clause_to_clause_subsumption:       214
% 2.67/0.99  res_orphan_elimination:                 0
% 2.67/0.99  res_tautology_del:                      81
% 2.67/0.99  res_num_eq_res_simplified:              0
% 2.67/0.99  res_num_sel_changes:                    0
% 2.67/0.99  res_moves_from_active_to_pass:          0
% 2.67/0.99  
% 2.67/0.99  ------ Superposition
% 2.67/0.99  
% 2.67/0.99  sup_time_total:                         0.
% 2.67/0.99  sup_time_generating:                    0.
% 2.67/0.99  sup_time_sim_full:                      0.
% 2.67/0.99  sup_time_sim_immed:                     0.
% 2.67/0.99  
% 2.67/0.99  sup_num_of_clauses:                     34
% 2.67/0.99  sup_num_in_active:                      24
% 2.67/0.99  sup_num_in_passive:                     10
% 2.67/0.99  sup_num_of_loops:                       69
% 2.67/0.99  sup_fw_superposition:                   30
% 2.67/0.99  sup_bw_superposition:                   34
% 2.67/0.99  sup_immediate_simplified:               70
% 2.67/0.99  sup_given_eliminated:                   0
% 2.67/0.99  comparisons_done:                       0
% 2.67/0.99  comparisons_avoided:                    5
% 2.67/0.99  
% 2.67/0.99  ------ Simplifications
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  sim_fw_subset_subsumed:                 7
% 2.67/0.99  sim_bw_subset_subsumed:                 4
% 2.67/0.99  sim_fw_subsumed:                        16
% 2.67/0.99  sim_bw_subsumed:                        4
% 2.67/0.99  sim_fw_subsumption_res:                 3
% 2.67/0.99  sim_bw_subsumption_res:                 0
% 2.67/0.99  sim_tautology_del:                      4
% 2.67/0.99  sim_eq_tautology_del:                   8
% 2.67/0.99  sim_eq_res_simp:                        14
% 2.67/0.99  sim_fw_demodulated:                     2
% 2.67/0.99  sim_bw_demodulated:                     48
% 2.67/0.99  sim_light_normalised:                   55
% 2.67/0.99  sim_joinable_taut:                      0
% 2.67/0.99  sim_joinable_simp:                      0
% 2.67/0.99  sim_ac_normalised:                      0
% 2.67/0.99  sim_smt_subsumption:                    0
% 2.67/0.99  
%------------------------------------------------------------------------------
