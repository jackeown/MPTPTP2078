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
% DateTime   : Thu Dec  3 12:02:41 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  169 (11316 expanded)
%              Number of clauses        :  111 (3397 expanded)
%              Number of leaves         :   15 (2249 expanded)
%              Depth                    :   30
%              Number of atoms          :  493 (62565 expanded)
%              Number of equality atoms :  250 (11963 expanded)
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f39])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
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

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_516,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_30])).

cnf(c_1080,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1084,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3370,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1080,c_1084])).

cnf(c_3549,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_516,c_3370])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1083,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2321,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1080,c_1083])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2333,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2321,c_28])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_304,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_305,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_307,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_32])).

cnf(c_1078,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1358,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1078,c_32,c_30,c_305,c_1350])).

cnf(c_2444,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2333,c_1358])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1081,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2703,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2444,c_1081])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_318,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_319,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_321,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_32])).

cnf(c_1077,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_1354,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1077,c_32,c_30,c_319,c_1350])).

cnf(c_2704,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2703,c_1354])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1351,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1428,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1429,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1431,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1432,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1431])).

cnf(c_3081,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2704,c_33,c_35,c_1351,c_1429,c_1432])).

cnf(c_3578,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_3081])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_524,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_525,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_537,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_525,c_13])).

cnf(c_1068,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_1417,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1068,c_1354,c_1358])).

cnf(c_2443,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2333,c_1417])).

cnf(c_2447,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2443])).

cnf(c_2918,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(sK2) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2447,c_33,c_35,c_1351,c_1417,c_1429,c_2333])).

cnf(c_2919,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2918])).

cnf(c_3579,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_2919])).

cnf(c_3588,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3578,c_3579])).

cnf(c_3724,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3588,c_3081])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3796,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3724,c_4])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_442,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1072,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1255,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1072,c_4])).

cnf(c_1670,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1255,c_33,c_35,c_1351,c_1429])).

cnf(c_1671,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1670])).

cnf(c_3731,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3588,c_1671])).

cnf(c_3768,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3731])).

cnf(c_3772,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3768,c_4])).

cnf(c_3799,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3796,c_3772])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1085,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3265,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_1085])).

cnf(c_3721,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3588,c_3265])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_99,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_615,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1489,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_1490,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_1492,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_1633,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2869,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_2870,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2869])).

cnf(c_4551,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3721,c_35,c_99,c_1492,c_2870,c_3588])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1091,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4557,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4551,c_1091])).

cnf(c_3267,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_1085])).

cnf(c_3269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1085])).

cnf(c_4722,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3796,c_3269])).

cnf(c_4738,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4722])).

cnf(c_6180,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3267,c_99,c_4738])).

cnf(c_6184,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6180,c_4557])).

cnf(c_6188,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6184,c_1091])).

cnf(c_6405,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3799,c_4557,c_6188])).

cnf(c_4753,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4557,c_1354])).

cnf(c_6292,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6188,c_4753])).

cnf(c_3729,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3588,c_2333])).

cnf(c_4750,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4557,c_3729])).

cnf(c_6294,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6292,c_4750])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1089,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3367,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1089,c_1084])).

cnf(c_6355,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6294,c_3367])).

cnf(c_6406,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6405,c_6355])).

cnf(c_6407,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6406])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.75/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.75/1.00  
% 2.75/1.00  ------  iProver source info
% 2.75/1.00  
% 2.75/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.75/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.75/1.00  git: non_committed_changes: false
% 2.75/1.00  git: last_make_outside_of_git: false
% 2.75/1.00  
% 2.75/1.00  ------ 
% 2.75/1.00  
% 2.75/1.00  ------ Input Options
% 2.75/1.00  
% 2.75/1.00  --out_options                           all
% 2.75/1.00  --tptp_safe_out                         true
% 2.75/1.00  --problem_path                          ""
% 2.75/1.00  --include_path                          ""
% 2.75/1.00  --clausifier                            res/vclausify_rel
% 2.75/1.00  --clausifier_options                    --mode clausify
% 2.75/1.00  --stdin                                 false
% 2.75/1.00  --stats_out                             all
% 2.75/1.00  
% 2.75/1.00  ------ General Options
% 2.75/1.00  
% 2.75/1.00  --fof                                   false
% 2.75/1.00  --time_out_real                         305.
% 2.75/1.00  --time_out_virtual                      -1.
% 2.75/1.00  --symbol_type_check                     false
% 2.75/1.00  --clausify_out                          false
% 2.75/1.00  --sig_cnt_out                           false
% 2.75/1.00  --trig_cnt_out                          false
% 2.75/1.00  --trig_cnt_out_tolerance                1.
% 2.75/1.00  --trig_cnt_out_sk_spl                   false
% 2.75/1.00  --abstr_cl_out                          false
% 2.75/1.00  
% 2.75/1.00  ------ Global Options
% 2.75/1.00  
% 2.75/1.00  --schedule                              default
% 2.75/1.00  --add_important_lit                     false
% 2.75/1.00  --prop_solver_per_cl                    1000
% 2.75/1.00  --min_unsat_core                        false
% 2.75/1.00  --soft_assumptions                      false
% 2.75/1.00  --soft_lemma_size                       3
% 2.75/1.00  --prop_impl_unit_size                   0
% 2.75/1.00  --prop_impl_unit                        []
% 2.75/1.00  --share_sel_clauses                     true
% 2.75/1.00  --reset_solvers                         false
% 2.75/1.00  --bc_imp_inh                            [conj_cone]
% 2.75/1.00  --conj_cone_tolerance                   3.
% 2.75/1.00  --extra_neg_conj                        none
% 2.75/1.00  --large_theory_mode                     true
% 2.75/1.00  --prolific_symb_bound                   200
% 2.75/1.00  --lt_threshold                          2000
% 2.75/1.00  --clause_weak_htbl                      true
% 2.75/1.00  --gc_record_bc_elim                     false
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing Options
% 2.75/1.00  
% 2.75/1.00  --preprocessing_flag                    true
% 2.75/1.00  --time_out_prep_mult                    0.1
% 2.75/1.00  --splitting_mode                        input
% 2.75/1.00  --splitting_grd                         true
% 2.75/1.00  --splitting_cvd                         false
% 2.75/1.00  --splitting_cvd_svl                     false
% 2.75/1.00  --splitting_nvd                         32
% 2.75/1.00  --sub_typing                            true
% 2.75/1.00  --prep_gs_sim                           true
% 2.75/1.00  --prep_unflatten                        true
% 2.75/1.00  --prep_res_sim                          true
% 2.75/1.00  --prep_upred                            true
% 2.75/1.00  --prep_sem_filter                       exhaustive
% 2.75/1.00  --prep_sem_filter_out                   false
% 2.75/1.00  --pred_elim                             true
% 2.75/1.00  --res_sim_input                         true
% 2.75/1.00  --eq_ax_congr_red                       true
% 2.75/1.00  --pure_diseq_elim                       true
% 2.75/1.00  --brand_transform                       false
% 2.75/1.00  --non_eq_to_eq                          false
% 2.75/1.00  --prep_def_merge                        true
% 2.75/1.00  --prep_def_merge_prop_impl              false
% 2.75/1.00  --prep_def_merge_mbd                    true
% 2.75/1.00  --prep_def_merge_tr_red                 false
% 2.75/1.00  --prep_def_merge_tr_cl                  false
% 2.75/1.00  --smt_preprocessing                     true
% 2.75/1.00  --smt_ac_axioms                         fast
% 2.75/1.00  --preprocessed_out                      false
% 2.75/1.00  --preprocessed_stats                    false
% 2.75/1.00  
% 2.75/1.00  ------ Abstraction refinement Options
% 2.75/1.00  
% 2.75/1.00  --abstr_ref                             []
% 2.75/1.00  --abstr_ref_prep                        false
% 2.75/1.00  --abstr_ref_until_sat                   false
% 2.75/1.00  --abstr_ref_sig_restrict                funpre
% 2.75/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/1.00  --abstr_ref_under                       []
% 2.75/1.00  
% 2.75/1.00  ------ SAT Options
% 2.75/1.00  
% 2.75/1.00  --sat_mode                              false
% 2.75/1.00  --sat_fm_restart_options                ""
% 2.75/1.00  --sat_gr_def                            false
% 2.75/1.00  --sat_epr_types                         true
% 2.75/1.00  --sat_non_cyclic_types                  false
% 2.75/1.00  --sat_finite_models                     false
% 2.75/1.00  --sat_fm_lemmas                         false
% 2.75/1.00  --sat_fm_prep                           false
% 2.75/1.00  --sat_fm_uc_incr                        true
% 2.75/1.00  --sat_out_model                         small
% 2.75/1.00  --sat_out_clauses                       false
% 2.75/1.00  
% 2.75/1.00  ------ QBF Options
% 2.75/1.00  
% 2.75/1.00  --qbf_mode                              false
% 2.75/1.00  --qbf_elim_univ                         false
% 2.75/1.00  --qbf_dom_inst                          none
% 2.75/1.00  --qbf_dom_pre_inst                      false
% 2.75/1.00  --qbf_sk_in                             false
% 2.75/1.00  --qbf_pred_elim                         true
% 2.75/1.00  --qbf_split                             512
% 2.75/1.00  
% 2.75/1.00  ------ BMC1 Options
% 2.75/1.00  
% 2.75/1.00  --bmc1_incremental                      false
% 2.75/1.00  --bmc1_axioms                           reachable_all
% 2.75/1.00  --bmc1_min_bound                        0
% 2.75/1.00  --bmc1_max_bound                        -1
% 2.75/1.00  --bmc1_max_bound_default                -1
% 2.75/1.00  --bmc1_symbol_reachability              true
% 2.75/1.00  --bmc1_property_lemmas                  false
% 2.75/1.00  --bmc1_k_induction                      false
% 2.75/1.00  --bmc1_non_equiv_states                 false
% 2.75/1.00  --bmc1_deadlock                         false
% 2.75/1.00  --bmc1_ucm                              false
% 2.75/1.00  --bmc1_add_unsat_core                   none
% 2.75/1.00  --bmc1_unsat_core_children              false
% 2.75/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/1.00  --bmc1_out_stat                         full
% 2.75/1.00  --bmc1_ground_init                      false
% 2.75/1.00  --bmc1_pre_inst_next_state              false
% 2.75/1.00  --bmc1_pre_inst_state                   false
% 2.75/1.00  --bmc1_pre_inst_reach_state             false
% 2.75/1.00  --bmc1_out_unsat_core                   false
% 2.75/1.00  --bmc1_aig_witness_out                  false
% 2.75/1.00  --bmc1_verbose                          false
% 2.75/1.00  --bmc1_dump_clauses_tptp                false
% 2.75/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.75/1.00  --bmc1_dump_file                        -
% 2.75/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.75/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.75/1.00  --bmc1_ucm_extend_mode                  1
% 2.75/1.00  --bmc1_ucm_init_mode                    2
% 2.75/1.00  --bmc1_ucm_cone_mode                    none
% 2.75/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.75/1.00  --bmc1_ucm_relax_model                  4
% 2.75/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.75/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/1.00  --bmc1_ucm_layered_model                none
% 2.75/1.00  --bmc1_ucm_max_lemma_size               10
% 2.75/1.00  
% 2.75/1.00  ------ AIG Options
% 2.75/1.00  
% 2.75/1.00  --aig_mode                              false
% 2.75/1.00  
% 2.75/1.00  ------ Instantiation Options
% 2.75/1.00  
% 2.75/1.00  --instantiation_flag                    true
% 2.75/1.00  --inst_sos_flag                         false
% 2.75/1.00  --inst_sos_phase                        true
% 2.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel_side                     num_symb
% 2.75/1.00  --inst_solver_per_active                1400
% 2.75/1.00  --inst_solver_calls_frac                1.
% 2.75/1.00  --inst_passive_queue_type               priority_queues
% 2.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/1.00  --inst_passive_queues_freq              [25;2]
% 2.75/1.00  --inst_dismatching                      true
% 2.75/1.00  --inst_eager_unprocessed_to_passive     true
% 2.75/1.00  --inst_prop_sim_given                   true
% 2.75/1.00  --inst_prop_sim_new                     false
% 2.75/1.00  --inst_subs_new                         false
% 2.75/1.00  --inst_eq_res_simp                      false
% 2.75/1.00  --inst_subs_given                       false
% 2.75/1.00  --inst_orphan_elimination               true
% 2.75/1.00  --inst_learning_loop_flag               true
% 2.75/1.00  --inst_learning_start                   3000
% 2.75/1.00  --inst_learning_factor                  2
% 2.75/1.00  --inst_start_prop_sim_after_learn       3
% 2.75/1.00  --inst_sel_renew                        solver
% 2.75/1.00  --inst_lit_activity_flag                true
% 2.75/1.00  --inst_restr_to_given                   false
% 2.75/1.00  --inst_activity_threshold               500
% 2.75/1.00  --inst_out_proof                        true
% 2.75/1.00  
% 2.75/1.00  ------ Resolution Options
% 2.75/1.00  
% 2.75/1.00  --resolution_flag                       true
% 2.75/1.00  --res_lit_sel                           adaptive
% 2.75/1.00  --res_lit_sel_side                      none
% 2.75/1.00  --res_ordering                          kbo
% 2.75/1.00  --res_to_prop_solver                    active
% 2.75/1.00  --res_prop_simpl_new                    false
% 2.75/1.00  --res_prop_simpl_given                  true
% 2.75/1.00  --res_passive_queue_type                priority_queues
% 2.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/1.00  --res_passive_queues_freq               [15;5]
% 2.75/1.00  --res_forward_subs                      full
% 2.75/1.00  --res_backward_subs                     full
% 2.75/1.00  --res_forward_subs_resolution           true
% 2.75/1.00  --res_backward_subs_resolution          true
% 2.75/1.00  --res_orphan_elimination                true
% 2.75/1.00  --res_time_limit                        2.
% 2.75/1.00  --res_out_proof                         true
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Options
% 2.75/1.00  
% 2.75/1.00  --superposition_flag                    true
% 2.75/1.00  --sup_passive_queue_type                priority_queues
% 2.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.75/1.00  --demod_completeness_check              fast
% 2.75/1.00  --demod_use_ground                      true
% 2.75/1.00  --sup_to_prop_solver                    passive
% 2.75/1.00  --sup_prop_simpl_new                    true
% 2.75/1.00  --sup_prop_simpl_given                  true
% 2.75/1.00  --sup_fun_splitting                     false
% 2.75/1.00  --sup_smt_interval                      50000
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Simplification Setup
% 2.75/1.00  
% 2.75/1.00  --sup_indices_passive                   []
% 2.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_full_bw                           [BwDemod]
% 2.75/1.00  --sup_immed_triv                        [TrivRules]
% 2.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_immed_bw_main                     []
% 2.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  
% 2.75/1.00  ------ Combination Options
% 2.75/1.00  
% 2.75/1.00  --comb_res_mult                         3
% 2.75/1.00  --comb_sup_mult                         2
% 2.75/1.00  --comb_inst_mult                        10
% 2.75/1.00  
% 2.75/1.00  ------ Debug Options
% 2.75/1.00  
% 2.75/1.00  --dbg_backtrace                         false
% 2.75/1.00  --dbg_dump_prop_clauses                 false
% 2.75/1.00  --dbg_dump_prop_clauses_file            -
% 2.75/1.00  --dbg_out_stat                          false
% 2.75/1.00  ------ Parsing...
% 2.75/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.75/1.00  ------ Proving...
% 2.75/1.00  ------ Problem Properties 
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  clauses                                 33
% 2.75/1.00  conjectures                             3
% 2.75/1.00  EPR                                     4
% 2.75/1.00  Horn                                    28
% 2.75/1.00  unary                                   10
% 2.75/1.00  binary                                  7
% 2.75/1.00  lits                                    84
% 2.75/1.00  lits eq                                 39
% 2.75/1.00  fd_pure                                 0
% 2.75/1.00  fd_pseudo                               0
% 2.75/1.00  fd_cond                                 3
% 2.75/1.00  fd_pseudo_cond                          1
% 2.75/1.00  AC symbols                              0
% 2.75/1.00  
% 2.75/1.00  ------ Schedule dynamic 5 is on 
% 2.75/1.00  
% 2.75/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  ------ 
% 2.75/1.00  Current options:
% 2.75/1.00  ------ 
% 2.75/1.00  
% 2.75/1.00  ------ Input Options
% 2.75/1.00  
% 2.75/1.00  --out_options                           all
% 2.75/1.00  --tptp_safe_out                         true
% 2.75/1.00  --problem_path                          ""
% 2.75/1.00  --include_path                          ""
% 2.75/1.00  --clausifier                            res/vclausify_rel
% 2.75/1.00  --clausifier_options                    --mode clausify
% 2.75/1.00  --stdin                                 false
% 2.75/1.00  --stats_out                             all
% 2.75/1.00  
% 2.75/1.00  ------ General Options
% 2.75/1.00  
% 2.75/1.00  --fof                                   false
% 2.75/1.00  --time_out_real                         305.
% 2.75/1.00  --time_out_virtual                      -1.
% 2.75/1.00  --symbol_type_check                     false
% 2.75/1.00  --clausify_out                          false
% 2.75/1.00  --sig_cnt_out                           false
% 2.75/1.00  --trig_cnt_out                          false
% 2.75/1.00  --trig_cnt_out_tolerance                1.
% 2.75/1.00  --trig_cnt_out_sk_spl                   false
% 2.75/1.00  --abstr_cl_out                          false
% 2.75/1.00  
% 2.75/1.00  ------ Global Options
% 2.75/1.00  
% 2.75/1.00  --schedule                              default
% 2.75/1.00  --add_important_lit                     false
% 2.75/1.00  --prop_solver_per_cl                    1000
% 2.75/1.00  --min_unsat_core                        false
% 2.75/1.00  --soft_assumptions                      false
% 2.75/1.00  --soft_lemma_size                       3
% 2.75/1.00  --prop_impl_unit_size                   0
% 2.75/1.00  --prop_impl_unit                        []
% 2.75/1.00  --share_sel_clauses                     true
% 2.75/1.00  --reset_solvers                         false
% 2.75/1.00  --bc_imp_inh                            [conj_cone]
% 2.75/1.00  --conj_cone_tolerance                   3.
% 2.75/1.00  --extra_neg_conj                        none
% 2.75/1.00  --large_theory_mode                     true
% 2.75/1.00  --prolific_symb_bound                   200
% 2.75/1.00  --lt_threshold                          2000
% 2.75/1.00  --clause_weak_htbl                      true
% 2.75/1.00  --gc_record_bc_elim                     false
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing Options
% 2.75/1.00  
% 2.75/1.00  --preprocessing_flag                    true
% 2.75/1.00  --time_out_prep_mult                    0.1
% 2.75/1.00  --splitting_mode                        input
% 2.75/1.00  --splitting_grd                         true
% 2.75/1.00  --splitting_cvd                         false
% 2.75/1.00  --splitting_cvd_svl                     false
% 2.75/1.00  --splitting_nvd                         32
% 2.75/1.00  --sub_typing                            true
% 2.75/1.00  --prep_gs_sim                           true
% 2.75/1.00  --prep_unflatten                        true
% 2.75/1.00  --prep_res_sim                          true
% 2.75/1.00  --prep_upred                            true
% 2.75/1.00  --prep_sem_filter                       exhaustive
% 2.75/1.00  --prep_sem_filter_out                   false
% 2.75/1.00  --pred_elim                             true
% 2.75/1.00  --res_sim_input                         true
% 2.75/1.00  --eq_ax_congr_red                       true
% 2.75/1.00  --pure_diseq_elim                       true
% 2.75/1.00  --brand_transform                       false
% 2.75/1.00  --non_eq_to_eq                          false
% 2.75/1.00  --prep_def_merge                        true
% 2.75/1.00  --prep_def_merge_prop_impl              false
% 2.75/1.00  --prep_def_merge_mbd                    true
% 2.75/1.00  --prep_def_merge_tr_red                 false
% 2.75/1.00  --prep_def_merge_tr_cl                  false
% 2.75/1.00  --smt_preprocessing                     true
% 2.75/1.00  --smt_ac_axioms                         fast
% 2.75/1.00  --preprocessed_out                      false
% 2.75/1.00  --preprocessed_stats                    false
% 2.75/1.00  
% 2.75/1.00  ------ Abstraction refinement Options
% 2.75/1.00  
% 2.75/1.00  --abstr_ref                             []
% 2.75/1.00  --abstr_ref_prep                        false
% 2.75/1.00  --abstr_ref_until_sat                   false
% 2.75/1.00  --abstr_ref_sig_restrict                funpre
% 2.75/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/1.00  --abstr_ref_under                       []
% 2.75/1.00  
% 2.75/1.00  ------ SAT Options
% 2.75/1.00  
% 2.75/1.00  --sat_mode                              false
% 2.75/1.00  --sat_fm_restart_options                ""
% 2.75/1.00  --sat_gr_def                            false
% 2.75/1.00  --sat_epr_types                         true
% 2.75/1.00  --sat_non_cyclic_types                  false
% 2.75/1.00  --sat_finite_models                     false
% 2.75/1.00  --sat_fm_lemmas                         false
% 2.75/1.00  --sat_fm_prep                           false
% 2.75/1.00  --sat_fm_uc_incr                        true
% 2.75/1.00  --sat_out_model                         small
% 2.75/1.00  --sat_out_clauses                       false
% 2.75/1.00  
% 2.75/1.00  ------ QBF Options
% 2.75/1.00  
% 2.75/1.00  --qbf_mode                              false
% 2.75/1.00  --qbf_elim_univ                         false
% 2.75/1.00  --qbf_dom_inst                          none
% 2.75/1.00  --qbf_dom_pre_inst                      false
% 2.75/1.00  --qbf_sk_in                             false
% 2.75/1.00  --qbf_pred_elim                         true
% 2.75/1.00  --qbf_split                             512
% 2.75/1.00  
% 2.75/1.00  ------ BMC1 Options
% 2.75/1.00  
% 2.75/1.00  --bmc1_incremental                      false
% 2.75/1.00  --bmc1_axioms                           reachable_all
% 2.75/1.00  --bmc1_min_bound                        0
% 2.75/1.00  --bmc1_max_bound                        -1
% 2.75/1.00  --bmc1_max_bound_default                -1
% 2.75/1.00  --bmc1_symbol_reachability              true
% 2.75/1.00  --bmc1_property_lemmas                  false
% 2.75/1.00  --bmc1_k_induction                      false
% 2.75/1.00  --bmc1_non_equiv_states                 false
% 2.75/1.00  --bmc1_deadlock                         false
% 2.75/1.00  --bmc1_ucm                              false
% 2.75/1.00  --bmc1_add_unsat_core                   none
% 2.75/1.00  --bmc1_unsat_core_children              false
% 2.75/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/1.00  --bmc1_out_stat                         full
% 2.75/1.00  --bmc1_ground_init                      false
% 2.75/1.00  --bmc1_pre_inst_next_state              false
% 2.75/1.00  --bmc1_pre_inst_state                   false
% 2.75/1.00  --bmc1_pre_inst_reach_state             false
% 2.75/1.00  --bmc1_out_unsat_core                   false
% 2.75/1.00  --bmc1_aig_witness_out                  false
% 2.75/1.00  --bmc1_verbose                          false
% 2.75/1.00  --bmc1_dump_clauses_tptp                false
% 2.75/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.75/1.00  --bmc1_dump_file                        -
% 2.75/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.75/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.75/1.00  --bmc1_ucm_extend_mode                  1
% 2.75/1.00  --bmc1_ucm_init_mode                    2
% 2.75/1.00  --bmc1_ucm_cone_mode                    none
% 2.75/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.75/1.00  --bmc1_ucm_relax_model                  4
% 2.75/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.75/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/1.00  --bmc1_ucm_layered_model                none
% 2.75/1.00  --bmc1_ucm_max_lemma_size               10
% 2.75/1.00  
% 2.75/1.00  ------ AIG Options
% 2.75/1.00  
% 2.75/1.00  --aig_mode                              false
% 2.75/1.00  
% 2.75/1.00  ------ Instantiation Options
% 2.75/1.00  
% 2.75/1.00  --instantiation_flag                    true
% 2.75/1.00  --inst_sos_flag                         false
% 2.75/1.00  --inst_sos_phase                        true
% 2.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/1.00  --inst_lit_sel_side                     none
% 2.75/1.00  --inst_solver_per_active                1400
% 2.75/1.00  --inst_solver_calls_frac                1.
% 2.75/1.00  --inst_passive_queue_type               priority_queues
% 2.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/1.00  --inst_passive_queues_freq              [25;2]
% 2.75/1.00  --inst_dismatching                      true
% 2.75/1.00  --inst_eager_unprocessed_to_passive     true
% 2.75/1.00  --inst_prop_sim_given                   true
% 2.75/1.00  --inst_prop_sim_new                     false
% 2.75/1.00  --inst_subs_new                         false
% 2.75/1.00  --inst_eq_res_simp                      false
% 2.75/1.00  --inst_subs_given                       false
% 2.75/1.00  --inst_orphan_elimination               true
% 2.75/1.00  --inst_learning_loop_flag               true
% 2.75/1.00  --inst_learning_start                   3000
% 2.75/1.00  --inst_learning_factor                  2
% 2.75/1.00  --inst_start_prop_sim_after_learn       3
% 2.75/1.00  --inst_sel_renew                        solver
% 2.75/1.00  --inst_lit_activity_flag                true
% 2.75/1.00  --inst_restr_to_given                   false
% 2.75/1.00  --inst_activity_threshold               500
% 2.75/1.00  --inst_out_proof                        true
% 2.75/1.00  
% 2.75/1.00  ------ Resolution Options
% 2.75/1.00  
% 2.75/1.00  --resolution_flag                       false
% 2.75/1.00  --res_lit_sel                           adaptive
% 2.75/1.00  --res_lit_sel_side                      none
% 2.75/1.00  --res_ordering                          kbo
% 2.75/1.00  --res_to_prop_solver                    active
% 2.75/1.00  --res_prop_simpl_new                    false
% 2.75/1.00  --res_prop_simpl_given                  true
% 2.75/1.00  --res_passive_queue_type                priority_queues
% 2.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/1.00  --res_passive_queues_freq               [15;5]
% 2.75/1.00  --res_forward_subs                      full
% 2.75/1.00  --res_backward_subs                     full
% 2.75/1.00  --res_forward_subs_resolution           true
% 2.75/1.00  --res_backward_subs_resolution          true
% 2.75/1.00  --res_orphan_elimination                true
% 2.75/1.00  --res_time_limit                        2.
% 2.75/1.00  --res_out_proof                         true
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Options
% 2.75/1.00  
% 2.75/1.00  --superposition_flag                    true
% 2.75/1.00  --sup_passive_queue_type                priority_queues
% 2.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.75/1.00  --demod_completeness_check              fast
% 2.75/1.00  --demod_use_ground                      true
% 2.75/1.00  --sup_to_prop_solver                    passive
% 2.75/1.00  --sup_prop_simpl_new                    true
% 2.75/1.00  --sup_prop_simpl_given                  true
% 2.75/1.00  --sup_fun_splitting                     false
% 2.75/1.00  --sup_smt_interval                      50000
% 2.75/1.00  
% 2.75/1.00  ------ Superposition Simplification Setup
% 2.75/1.00  
% 2.75/1.00  --sup_indices_passive                   []
% 2.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_full_bw                           [BwDemod]
% 2.75/1.00  --sup_immed_triv                        [TrivRules]
% 2.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_immed_bw_main                     []
% 2.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/1.00  
% 2.75/1.00  ------ Combination Options
% 2.75/1.00  
% 2.75/1.00  --comb_res_mult                         3
% 2.75/1.00  --comb_sup_mult                         2
% 2.75/1.00  --comb_inst_mult                        10
% 2.75/1.00  
% 2.75/1.00  ------ Debug Options
% 2.75/1.00  
% 2.75/1.00  --dbg_backtrace                         false
% 2.75/1.00  --dbg_dump_prop_clauses                 false
% 2.75/1.00  --dbg_dump_prop_clauses_file            -
% 2.75/1.00  --dbg_out_stat                          false
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  ------ Proving...
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  % SZS status Theorem for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00   Resolution empty clause
% 2.75/1.00  
% 2.75/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  fof(f15,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f30,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(ennf_transformation,[],[f15])).
% 2.75/1.00  
% 2.75/1.00  fof(f31,plain,(
% 2.75/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(flattening,[],[f30])).
% 2.75/1.00  
% 2.75/1.00  fof(f38,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(nnf_transformation,[],[f31])).
% 2.75/1.00  
% 2.75/1.00  fof(f59,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f38])).
% 2.75/1.00  
% 2.75/1.00  fof(f17,conjecture,(
% 2.75/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f18,negated_conjecture,(
% 2.75/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.75/1.00    inference(negated_conjecture,[],[f17])).
% 2.75/1.00  
% 2.75/1.00  fof(f34,plain,(
% 2.75/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.75/1.00    inference(ennf_transformation,[],[f18])).
% 2.75/1.00  
% 2.75/1.00  fof(f35,plain,(
% 2.75/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.75/1.00    inference(flattening,[],[f34])).
% 2.75/1.00  
% 2.75/1.00  fof(f39,plain,(
% 2.75/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.75/1.00    introduced(choice_axiom,[])).
% 2.75/1.00  
% 2.75/1.00  fof(f40,plain,(
% 2.75/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f39])).
% 2.75/1.00  
% 2.75/1.00  fof(f69,plain,(
% 2.75/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.75/1.00    inference(cnf_transformation,[],[f40])).
% 2.75/1.00  
% 2.75/1.00  fof(f70,plain,(
% 2.75/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.75/1.00    inference(cnf_transformation,[],[f40])).
% 2.75/1.00  
% 2.75/1.00  fof(f12,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f28,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(ennf_transformation,[],[f12])).
% 2.75/1.00  
% 2.75/1.00  fof(f56,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f28])).
% 2.75/1.00  
% 2.75/1.00  fof(f13,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f29,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(ennf_transformation,[],[f13])).
% 2.75/1.00  
% 2.75/1.00  fof(f57,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f29])).
% 2.75/1.00  
% 2.75/1.00  fof(f72,plain,(
% 2.75/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.75/1.00    inference(cnf_transformation,[],[f40])).
% 2.75/1.00  
% 2.75/1.00  fof(f9,axiom,(
% 2.75/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f24,plain,(
% 2.75/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.75/1.00    inference(ennf_transformation,[],[f9])).
% 2.75/1.00  
% 2.75/1.00  fof(f25,plain,(
% 2.75/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.75/1.00    inference(flattening,[],[f24])).
% 2.75/1.00  
% 2.75/1.00  fof(f52,plain,(
% 2.75/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f25])).
% 2.75/1.00  
% 2.75/1.00  fof(f71,plain,(
% 2.75/1.00    v2_funct_1(sK2)),
% 2.75/1.00    inference(cnf_transformation,[],[f40])).
% 2.75/1.00  
% 2.75/1.00  fof(f68,plain,(
% 2.75/1.00    v1_funct_1(sK2)),
% 2.75/1.00    inference(cnf_transformation,[],[f40])).
% 2.75/1.00  
% 2.75/1.00  fof(f10,axiom,(
% 2.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f26,plain,(
% 2.75/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.75/1.00    inference(ennf_transformation,[],[f10])).
% 2.75/1.00  
% 2.75/1.00  fof(f54,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f26])).
% 2.75/1.00  
% 2.75/1.00  fof(f16,axiom,(
% 2.75/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f32,plain,(
% 2.75/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.75/1.00    inference(ennf_transformation,[],[f16])).
% 2.75/1.00  
% 2.75/1.00  fof(f33,plain,(
% 2.75/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.75/1.00    inference(flattening,[],[f32])).
% 2.75/1.00  
% 2.75/1.00  fof(f67,plain,(
% 2.75/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f33])).
% 2.75/1.00  
% 2.75/1.00  fof(f53,plain,(
% 2.75/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f25])).
% 2.75/1.00  
% 2.75/1.00  fof(f8,axiom,(
% 2.75/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f22,plain,(
% 2.75/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.75/1.00    inference(ennf_transformation,[],[f8])).
% 2.75/1.00  
% 2.75/1.00  fof(f23,plain,(
% 2.75/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.75/1.00    inference(flattening,[],[f22])).
% 2.75/1.00  
% 2.75/1.00  fof(f51,plain,(
% 2.75/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f23])).
% 2.75/1.00  
% 2.75/1.00  fof(f50,plain,(
% 2.75/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f23])).
% 2.75/1.00  
% 2.75/1.00  fof(f66,plain,(
% 2.75/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f33])).
% 2.75/1.00  
% 2.75/1.00  fof(f73,plain,(
% 2.75/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.75/1.00    inference(cnf_transformation,[],[f40])).
% 2.75/1.00  
% 2.75/1.00  fof(f4,axiom,(
% 2.75/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f36,plain,(
% 2.75/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.75/1.00    inference(nnf_transformation,[],[f4])).
% 2.75/1.00  
% 2.75/1.00  fof(f37,plain,(
% 2.75/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.75/1.00    inference(flattening,[],[f36])).
% 2.75/1.00  
% 2.75/1.00  fof(f45,plain,(
% 2.75/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.75/1.00    inference(cnf_transformation,[],[f37])).
% 2.75/1.00  
% 2.75/1.00  fof(f75,plain,(
% 2.75/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.75/1.00    inference(equality_resolution,[],[f45])).
% 2.75/1.00  
% 2.75/1.00  fof(f62,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f38])).
% 2.75/1.00  
% 2.75/1.00  fof(f79,plain,(
% 2.75/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.75/1.00    inference(equality_resolution,[],[f62])).
% 2.75/1.00  
% 2.75/1.00  fof(f11,axiom,(
% 2.75/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f27,plain,(
% 2.75/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.75/1.00    inference(ennf_transformation,[],[f11])).
% 2.75/1.00  
% 2.75/1.00  fof(f55,plain,(
% 2.75/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f27])).
% 2.75/1.00  
% 2.75/1.00  fof(f1,axiom,(
% 2.75/1.00    v1_xboole_0(k1_xboole_0)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f41,plain,(
% 2.75/1.00    v1_xboole_0(k1_xboole_0)),
% 2.75/1.00    inference(cnf_transformation,[],[f1])).
% 2.75/1.00  
% 2.75/1.00  fof(f2,axiom,(
% 2.75/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f20,plain,(
% 2.75/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.75/1.00    inference(ennf_transformation,[],[f2])).
% 2.75/1.00  
% 2.75/1.00  fof(f42,plain,(
% 2.75/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.75/1.00    inference(cnf_transformation,[],[f20])).
% 2.75/1.00  
% 2.75/1.00  fof(f5,axiom,(
% 2.75/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/1.00  
% 2.75/1.00  fof(f47,plain,(
% 2.75/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.75/1.00    inference(cnf_transformation,[],[f5])).
% 2.75/1.00  
% 2.75/1.00  cnf(c_23,plain,
% 2.75/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.75/1.00      | k1_xboole_0 = X2 ),
% 2.75/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_31,negated_conjecture,
% 2.75/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.75/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_513,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.75/1.00      | sK0 != X1
% 2.75/1.00      | sK1 != X2
% 2.75/1.00      | sK2 != X0
% 2.75/1.00      | k1_xboole_0 = X2 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_514,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.75/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.75/1.00      | k1_xboole_0 = sK1 ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_513]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_30,negated_conjecture,
% 2.75/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.75/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_516,plain,
% 2.75/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_514,c_30]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1080,plain,
% 2.75/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_15,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1084,plain,
% 2.75/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.75/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3370,plain,
% 2.75/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1080,c_1084]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3549,plain,
% 2.75/1.00      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_516,c_3370]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_16,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1083,plain,
% 2.75/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.75/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2321,plain,
% 2.75/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1080,c_1083]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_28,negated_conjecture,
% 2.75/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.75/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2333,plain,
% 2.75/1.00      ( k2_relat_1(sK2) = sK1 ),
% 2.75/1.00      inference(light_normalisation,[status(thm)],[c_2321,c_28]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_12,plain,
% 2.75/1.00      ( ~ v2_funct_1(X0)
% 2.75/1.00      | ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X0)
% 2.75/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_29,negated_conjecture,
% 2.75/1.00      ( v2_funct_1(sK2) ),
% 2.75/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_304,plain,
% 2.75/1.00      ( ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X0)
% 2.75/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.75/1.00      | sK2 != X0 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_305,plain,
% 2.75/1.00      ( ~ v1_relat_1(sK2)
% 2.75/1.00      | ~ v1_funct_1(sK2)
% 2.75/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_304]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_32,negated_conjecture,
% 2.75/1.00      ( v1_funct_1(sK2) ),
% 2.75/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_307,plain,
% 2.75/1.00      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_305,c_32]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1078,plain,
% 2.75/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.75/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_13,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1350,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.75/1.00      | v1_relat_1(sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1358,plain,
% 2.75/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_1078,c_32,c_30,c_305,c_1350]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2444,plain,
% 2.75/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_2333,c_1358]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_24,plain,
% 2.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.75/1.00      | ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1081,plain,
% 2.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.75/1.00      | v1_relat_1(X0) != iProver_top
% 2.75/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2703,plain,
% 2.75/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 2.75/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_2444,c_1081]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_11,plain,
% 2.75/1.00      ( ~ v2_funct_1(X0)
% 2.75/1.00      | ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X0)
% 2.75/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_318,plain,
% 2.75/1.00      ( ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X0)
% 2.75/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.75/1.00      | sK2 != X0 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_319,plain,
% 2.75/1.00      ( ~ v1_relat_1(sK2)
% 2.75/1.00      | ~ v1_funct_1(sK2)
% 2.75/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_318]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_321,plain,
% 2.75/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.75/1.00      inference(global_propositional_subsumption,[status(thm)],[c_319,c_32]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1077,plain,
% 2.75/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.75/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1354,plain,
% 2.75/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_1077,c_32,c_30,c_319,c_1350]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2704,plain,
% 2.75/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.75/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(light_normalisation,[status(thm)],[c_2703,c_1354]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_33,plain,
% 2.75/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_35,plain,
% 2.75/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1351,plain,
% 2.75/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.75/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1350]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_9,plain,
% 2.75/1.00      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.75/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1428,plain,
% 2.75/1.00      ( ~ v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1429,plain,
% 2.75/1.00      ( v1_relat_1(sK2) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.75/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_10,plain,
% 2.75/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1431,plain,
% 2.75/1.00      ( v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) | ~ v1_funct_1(sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1432,plain,
% 2.75/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.75/1.00      | v1_relat_1(sK2) != iProver_top
% 2.75/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1431]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3081,plain,
% 2.75/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_2704,c_33,c_35,c_1351,c_1429,c_1432]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3578,plain,
% 2.75/1.00      ( sK1 = k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_3549,c_3081]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_25,plain,
% 2.75/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.75/1.00      | ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_27,negated_conjecture,
% 2.75/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.75/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.75/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.75/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_524,plain,
% 2.75/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.75/1.00      | ~ v1_relat_1(X0)
% 2.75/1.00      | ~ v1_funct_1(X0)
% 2.75/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.75/1.00      | k2_funct_1(sK2) != X0
% 2.75/1.00      | k1_relat_1(X0) != sK1
% 2.75/1.00      | k2_relat_1(X0) != sK0 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_525,plain,
% 2.75/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.75/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.75/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.75/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.75/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_524]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_537,plain,
% 2.75/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.75/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.75/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.75/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.75/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_525,c_13]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1068,plain,
% 2.75/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.75/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1417,plain,
% 2.75/1.00      ( k1_relat_1(sK2) != sK0
% 2.75/1.00      | k2_relat_1(sK2) != sK1
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(light_normalisation,[status(thm)],[c_1068,c_1354,c_1358]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2443,plain,
% 2.75/1.00      ( k1_relat_1(sK2) != sK0
% 2.75/1.00      | sK1 != sK1
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_2333,c_1417]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2447,plain,
% 2.75/1.00      ( k1_relat_1(sK2) != sK0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(equality_resolution_simp,[status(thm)],[c_2443]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2918,plain,
% 2.75/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | k1_relat_1(sK2) != sK0 ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_2447,c_33,c_35,c_1351,c_1417,c_1429,c_2333]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2919,plain,
% 2.75/1.00      ( k1_relat_1(sK2) != sK0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.75/1.00      inference(renaming,[status(thm)],[c_2918]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3579,plain,
% 2.75/1.00      ( sK1 = k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_3549,c_2919]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3588,plain,
% 2.75/1.00      ( sK1 = k1_xboole_0 ),
% 2.75/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3578,c_3579]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3724,plain,
% 2.75/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_3588,c_3081]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4,plain,
% 2.75/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.75/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3796,plain,
% 2.75/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_3724,c_4]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_20,plain,
% 2.75/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.75/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.75/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_441,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.75/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.75/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.75/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.75/1.00      | k2_funct_1(sK2) != X0
% 2.75/1.00      | sK0 != X1
% 2.75/1.00      | sK1 != k1_xboole_0 ),
% 2.75/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_442,plain,
% 2.75/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.75/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.75/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.75/1.00      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.75/1.00      | sK1 != k1_xboole_0 ),
% 2.75/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1072,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.75/1.00      | sK1 != k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1255,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.75/1.00      | sK1 != k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.75/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_1072,c_4]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1670,plain,
% 2.75/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | sK1 != k1_xboole_0
% 2.75/1.00      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_1255,c_33,c_35,c_1351,c_1429]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1671,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.75/1.00      | sK1 != k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.75/1.00      inference(renaming,[status(thm)],[c_1670]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3731,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.75/1.00      | k1_xboole_0 != k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_3588,c_1671]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3768,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.75/1.00      inference(equality_resolution_simp,[status(thm)],[c_3731]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3772,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.75/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_3768,c_4]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3799,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.75/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_3796,c_3772]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_14,plain,
% 2.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.75/1.00      | ~ v1_xboole_0(X2)
% 2.75/1.00      | v1_xboole_0(X0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1085,plain,
% 2.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.75/1.00      | v1_xboole_0(X2) != iProver_top
% 2.75/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3265,plain,
% 2.75/1.00      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1080,c_1085]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3721,plain,
% 2.75/1.00      ( v1_xboole_0(sK2) = iProver_top
% 2.75/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_3588,c_3265]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_0,plain,
% 2.75/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.75/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_99,plain,
% 2.75/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_615,plain,
% 2.75/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.75/1.00      theory(equality) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1489,plain,
% 2.75/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_615]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1490,plain,
% 2.75/1.00      ( sK1 != X0
% 2.75/1.00      | v1_xboole_0(X0) != iProver_top
% 2.75/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1489]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1492,plain,
% 2.75/1.00      ( sK1 != k1_xboole_0
% 2.75/1.00      | v1_xboole_0(sK1) = iProver_top
% 2.75/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1490]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1633,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.75/1.00      | ~ v1_xboole_0(X1)
% 2.75/1.00      | v1_xboole_0(sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2869,plain,
% 2.75/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.75/1.00      | ~ v1_xboole_0(sK1)
% 2.75/1.00      | v1_xboole_0(sK2) ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_1633]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_2870,plain,
% 2.75/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.75/1.00      | v1_xboole_0(sK1) != iProver_top
% 2.75/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2869]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4551,plain,
% 2.75/1.00      ( v1_xboole_0(sK2) = iProver_top ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_3721,c_35,c_99,c_1492,c_2870,c_3588]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1,plain,
% 2.75/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.75/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1091,plain,
% 2.75/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4557,plain,
% 2.75/1.00      ( sK2 = k1_xboole_0 ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_4551,c_1091]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3267,plain,
% 2.75/1.00      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 2.75/1.00      | v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_3081,c_1085]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3269,plain,
% 2.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.75/1.00      | v1_xboole_0(X1) != iProver_top
% 2.75/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_4,c_1085]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4722,plain,
% 2.75/1.00      ( v1_xboole_0(X0) != iProver_top
% 2.75/1.00      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_3796,c_3269]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4738,plain,
% 2.75/1.00      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 2.75/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.75/1.00      inference(instantiation,[status(thm)],[c_4722]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6180,plain,
% 2.75/1.00      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 2.75/1.00      inference(global_propositional_subsumption,
% 2.75/1.00                [status(thm)],
% 2.75/1.00                [c_3267,c_99,c_4738]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6184,plain,
% 2.75/1.00      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 2.75/1.00      inference(light_normalisation,[status(thm)],[c_6180,c_4557]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6188,plain,
% 2.75/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_6184,c_1091]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6405,plain,
% 2.75/1.00      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
% 2.75/1.00      inference(light_normalisation,[status(thm)],[c_3799,c_4557,c_6188]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4753,plain,
% 2.75/1.00      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_4557,c_1354]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6292,plain,
% 2.75/1.00      ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_6188,c_4753]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3729,plain,
% 2.75/1.00      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_3588,c_2333]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_4750,plain,
% 2.75/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_4557,c_3729]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6294,plain,
% 2.75/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.75/1.00      inference(light_normalisation,[status(thm)],[c_6292,c_4750]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6,plain,
% 2.75/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.75/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_1089,plain,
% 2.75/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.75/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_3367,plain,
% 2.75/1.00      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.75/1.00      inference(superposition,[status(thm)],[c_1089,c_1084]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6355,plain,
% 2.75/1.00      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_6294,c_3367]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6406,plain,
% 2.75/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.75/1.00      inference(demodulation,[status(thm)],[c_6405,c_6355]) ).
% 2.75/1.00  
% 2.75/1.00  cnf(c_6407,plain,
% 2.75/1.00      ( $false ),
% 2.75/1.00      inference(equality_resolution_simp,[status(thm)],[c_6406]) ).
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.75/1.00  
% 2.75/1.00  ------                               Statistics
% 2.75/1.00  
% 2.75/1.00  ------ General
% 2.75/1.00  
% 2.75/1.00  abstr_ref_over_cycles:                  0
% 2.75/1.00  abstr_ref_under_cycles:                 0
% 2.75/1.00  gc_basic_clause_elim:                   0
% 2.75/1.00  forced_gc_time:                         0
% 2.75/1.00  parsing_time:                           0.011
% 2.75/1.00  unif_index_cands_time:                  0.
% 2.75/1.00  unif_index_add_time:                    0.
% 2.75/1.00  orderings_time:                         0.
% 2.75/1.00  out_proof_time:                         0.012
% 2.75/1.00  total_time:                             0.197
% 2.75/1.00  num_of_symbols:                         49
% 2.75/1.00  num_of_terms:                           4822
% 2.75/1.00  
% 2.75/1.00  ------ Preprocessing
% 2.75/1.00  
% 2.75/1.00  num_of_splits:                          0
% 2.75/1.00  num_of_split_atoms:                     0
% 2.75/1.00  num_of_reused_defs:                     0
% 2.75/1.00  num_eq_ax_congr_red:                    4
% 2.75/1.00  num_of_sem_filtered_clauses:            1
% 2.75/1.00  num_of_subtypes:                        0
% 2.75/1.00  monotx_restored_types:                  0
% 2.75/1.00  sat_num_of_epr_types:                   0
% 2.75/1.00  sat_num_of_non_cyclic_types:            0
% 2.75/1.00  sat_guarded_non_collapsed_types:        0
% 2.75/1.00  num_pure_diseq_elim:                    0
% 2.75/1.00  simp_replaced_by:                       0
% 2.75/1.00  res_preprocessed:                       125
% 2.75/1.00  prep_upred:                             0
% 2.75/1.00  prep_unflattend:                        43
% 2.75/1.00  smt_new_axioms:                         0
% 2.75/1.00  pred_elim_cands:                        6
% 2.75/1.00  pred_elim:                              2
% 2.75/1.00  pred_elim_cl:                           -1
% 2.75/1.00  pred_elim_cycles:                       3
% 2.75/1.00  merged_defs:                            0
% 2.75/1.00  merged_defs_ncl:                        0
% 2.75/1.00  bin_hyper_res:                          0
% 2.75/1.00  prep_cycles:                            3
% 2.75/1.00  pred_elim_time:                         0.007
% 2.75/1.00  splitting_time:                         0.
% 2.75/1.00  sem_filter_time:                        0.
% 2.75/1.00  monotx_time:                            0.
% 2.75/1.00  subtype_inf_time:                       0.
% 2.75/1.00  
% 2.75/1.00  ------ Problem properties
% 2.75/1.00  
% 2.75/1.00  clauses:                                33
% 2.75/1.00  conjectures:                            3
% 2.75/1.00  epr:                                    4
% 2.75/1.00  horn:                                   28
% 2.75/1.00  ground:                                 14
% 2.75/1.00  unary:                                  10
% 2.75/1.00  binary:                                 7
% 2.75/1.00  lits:                                   84
% 2.75/1.00  lits_eq:                                39
% 2.75/1.00  fd_pure:                                0
% 2.75/1.00  fd_pseudo:                              0
% 2.75/1.00  fd_cond:                                3
% 2.75/1.00  fd_pseudo_cond:                         1
% 2.75/1.00  ac_symbols:                             0
% 2.75/1.00  
% 2.75/1.00  ------ Propositional Solver
% 2.75/1.00  
% 2.75/1.00  prop_solver_calls:                      24
% 2.75/1.00  prop_fast_solver_calls:                 947
% 2.75/1.00  smt_solver_calls:                       0
% 2.75/1.00  smt_fast_solver_calls:                  0
% 2.75/1.00  prop_num_of_clauses:                    2240
% 2.75/1.00  prop_preprocess_simplified:             7132
% 2.75/1.00  prop_fo_subsumed:                       32
% 2.75/1.00  prop_solver_time:                       0.
% 2.75/1.00  smt_solver_time:                        0.
% 2.75/1.00  smt_fast_solver_time:                   0.
% 2.75/1.00  prop_fast_solver_time:                  0.
% 2.75/1.00  prop_unsat_core_time:                   0.
% 2.75/1.00  
% 2.75/1.00  ------ QBF
% 2.75/1.00  
% 2.75/1.00  qbf_q_res:                              0
% 2.75/1.00  qbf_num_tautologies:                    0
% 2.75/1.00  qbf_prep_cycles:                        0
% 2.75/1.00  
% 2.75/1.00  ------ BMC1
% 2.75/1.00  
% 2.75/1.00  bmc1_current_bound:                     -1
% 2.75/1.00  bmc1_last_solved_bound:                 -1
% 2.75/1.00  bmc1_unsat_core_size:                   -1
% 2.75/1.00  bmc1_unsat_core_parents_size:           -1
% 2.75/1.00  bmc1_merge_next_fun:                    0
% 2.75/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.75/1.00  
% 2.75/1.00  ------ Instantiation
% 2.75/1.00  
% 2.75/1.00  inst_num_of_clauses:                    947
% 2.75/1.00  inst_num_in_passive:                    502
% 2.75/1.00  inst_num_in_active:                     399
% 2.75/1.00  inst_num_in_unprocessed:                46
% 2.75/1.00  inst_num_of_loops:                      500
% 2.75/1.00  inst_num_of_learning_restarts:          0
% 2.75/1.00  inst_num_moves_active_passive:          99
% 2.75/1.00  inst_lit_activity:                      0
% 2.75/1.00  inst_lit_activity_moves:                0
% 2.75/1.00  inst_num_tautologies:                   0
% 2.75/1.00  inst_num_prop_implied:                  0
% 2.75/1.00  inst_num_existing_simplified:           0
% 2.75/1.00  inst_num_eq_res_simplified:             0
% 2.75/1.00  inst_num_child_elim:                    0
% 2.75/1.00  inst_num_of_dismatching_blockings:      387
% 2.75/1.00  inst_num_of_non_proper_insts:           786
% 2.75/1.00  inst_num_of_duplicates:                 0
% 2.75/1.00  inst_inst_num_from_inst_to_res:         0
% 2.75/1.00  inst_dismatching_checking_time:         0.
% 2.75/1.00  
% 2.75/1.00  ------ Resolution
% 2.75/1.00  
% 2.75/1.00  res_num_of_clauses:                     0
% 2.75/1.00  res_num_in_passive:                     0
% 2.75/1.00  res_num_in_active:                      0
% 2.75/1.00  res_num_of_loops:                       128
% 2.75/1.00  res_forward_subset_subsumed:            41
% 2.75/1.00  res_backward_subset_subsumed:           0
% 2.75/1.00  res_forward_subsumed:                   0
% 2.75/1.00  res_backward_subsumed:                  0
% 2.75/1.00  res_forward_subsumption_resolution:     4
% 2.75/1.00  res_backward_subsumption_resolution:    0
% 2.75/1.00  res_clause_to_clause_subsumption:       233
% 2.75/1.00  res_orphan_elimination:                 0
% 2.75/1.00  res_tautology_del:                      60
% 2.75/1.00  res_num_eq_res_simplified:              0
% 2.75/1.00  res_num_sel_changes:                    0
% 2.75/1.00  res_moves_from_active_to_pass:          0
% 2.75/1.00  
% 2.75/1.00  ------ Superposition
% 2.75/1.00  
% 2.75/1.00  sup_time_total:                         0.
% 2.75/1.00  sup_time_generating:                    0.
% 2.75/1.00  sup_time_sim_full:                      0.
% 2.75/1.00  sup_time_sim_immed:                     0.
% 2.75/1.00  
% 2.75/1.00  sup_num_of_clauses:                     72
% 2.75/1.00  sup_num_in_active:                      48
% 2.75/1.00  sup_num_in_passive:                     24
% 2.75/1.00  sup_num_of_loops:                       98
% 2.75/1.00  sup_fw_superposition:                   64
% 2.75/1.00  sup_bw_superposition:                   39
% 2.75/1.00  sup_immediate_simplified:               69
% 2.75/1.00  sup_given_eliminated:                   3
% 2.75/1.00  comparisons_done:                       0
% 2.75/1.00  comparisons_avoided:                    13
% 2.75/1.00  
% 2.75/1.00  ------ Simplifications
% 2.75/1.00  
% 2.75/1.00  
% 2.75/1.00  sim_fw_subset_subsumed:                 12
% 2.75/1.00  sim_bw_subset_subsumed:                 3
% 2.75/1.00  sim_fw_subsumed:                        17
% 2.75/1.00  sim_bw_subsumed:                        5
% 2.75/1.00  sim_fw_subsumption_res:                 3
% 2.75/1.00  sim_bw_subsumption_res:                 3
% 2.75/1.00  sim_tautology_del:                      4
% 2.75/1.00  sim_eq_tautology_del:                   12
% 2.75/1.00  sim_eq_res_simp:                        3
% 2.75/1.00  sim_fw_demodulated:                     31
% 2.75/1.00  sim_bw_demodulated:                     48
% 2.75/1.00  sim_light_normalised:                   48
% 2.75/1.00  sim_joinable_taut:                      0
% 2.75/1.00  sim_joinable_simp:                      0
% 2.75/1.00  sim_ac_normalised:                      0
% 2.75/1.00  sim_smt_subsumption:                    0
% 2.75/1.00  
%------------------------------------------------------------------------------
