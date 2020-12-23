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
% DateTime   : Thu Dec  3 12:02:42 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  192 (4803 expanded)
%              Number of clauses        :  130 (1492 expanded)
%              Number of leaves         :   18 ( 957 expanded)
%              Depth                    :   28
%              Number of atoms          :  553 (25988 expanded)
%              Number of equality atoms :  298 (5106 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f31,plain,(
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

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f36,plain,
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

fof(f37,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f36])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1027,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1031,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2903,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1031])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_91,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_592,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1393,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1394,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1393])).

cnf(c_1396,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1542,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2148,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_2149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2148])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_493,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1030,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2504,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1027,c_1030])).

cnf(c_2535,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_493,c_2504])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1029,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2070,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1027,c_1029])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2082,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2070,c_26])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_501,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_502,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_514,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_502,c_12])).

cnf(c_1015,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_295,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_296,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_298,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_30])).

cnf(c_1024,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_1280,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1289,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1024,c_30,c_28,c_296,c_1280])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_281,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_282,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_284,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_30])).

cnf(c_1025,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_1293,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1025,c_30,c_28,c_282,c_1280])).

cnf(c_1336,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1015,c_1289,c_1293])).

cnf(c_2094,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2082,c_1336])).

cnf(c_2098,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2094])).

cnf(c_31,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1281,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1372,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1373,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1372])).

cnf(c_2787,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(sK2) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2098,c_31,c_33,c_1281,c_1336,c_1373,c_2082])).

cnf(c_2788,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2787])).

cnf(c_2793,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_2788])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1028,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2228,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1028])).

cnf(c_2095,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2082,c_1293])).

cnf(c_2240,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2228,c_2095])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1375,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1376,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_2874,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2240,c_31,c_33,c_1281,c_1373,c_1376])).

cnf(c_2879,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_2874])).

cnf(c_3181,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2903,c_33,c_91,c_1396,c_2149,c_2793,c_2879])).

cnf(c_1037,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1036,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1881,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1036])).

cnf(c_3186,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3181,c_1881])).

cnf(c_3199,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3186,c_2874])).

cnf(c_3220,plain,
    ( k2_relset_1(sK0,sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_3186,c_26])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1035,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2069,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1035,c_1029])).

cnf(c_6,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2085,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2069,c_6])).

cnf(c_3222,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3220,c_2085])).

cnf(c_3290,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3199,c_3222])).

cnf(c_7,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3292,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3290,c_7])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3293,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3292,c_3])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_419,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1019,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1194,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1019,c_3])).

cnf(c_1533,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1194,c_31,c_33,c_1281,c_1373])).

cnf(c_1534,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1533])).

cnf(c_3211,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3186,c_1534])).

cnf(c_3257,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3211,c_3222])).

cnf(c_3258,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3257])).

cnf(c_3262,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3258,c_3])).

cnf(c_3295,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3293,c_3262])).

cnf(c_2905,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2874,c_1031])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_87,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1395,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_1508,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK2))
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1509,plain,
    ( k1_relat_1(sK2) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1508])).

cnf(c_1511,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_591,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1334,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_1558,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_1560,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_597,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1559,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_1561,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_1589,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1591,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1903,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_1904,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_4040,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_28,c_7,c_86,c_87,c_0,c_91,c_1395,c_1511,c_1560,c_1561,c_1591,c_1904,c_2148,c_2793,c_2879])).

cnf(c_4044,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4040,c_3186])).

cnf(c_4047,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4044,c_1881])).

cnf(c_4218,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3295,c_4047])).

cnf(c_2502,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1035,c_1030])).

cnf(c_2524,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2502,c_7])).

cnf(c_4219,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4218,c_2524])).

cnf(c_4220,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4219])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.00/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.01  
% 3.00/1.01  ------  iProver source info
% 3.00/1.01  
% 3.00/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.01  git: non_committed_changes: false
% 3.00/1.01  git: last_make_outside_of_git: false
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     num_symb
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       true
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  ------ Parsing...
% 3.00/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.02  ------ Proving...
% 3.00/1.02  ------ Problem Properties 
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  clauses                                 31
% 3.00/1.02  conjectures                             3
% 3.00/1.02  EPR                                     3
% 3.00/1.02  Horn                                    26
% 3.00/1.02  unary                                   9
% 3.00/1.02  binary                                  6
% 3.00/1.02  lits                                    81
% 3.00/1.02  lits eq                                 38
% 3.00/1.02  fd_pure                                 0
% 3.00/1.02  fd_pseudo                               0
% 3.00/1.02  fd_cond                                 2
% 3.00/1.02  fd_pseudo_cond                          1
% 3.00/1.02  AC symbols                              0
% 3.00/1.02  
% 3.00/1.02  ------ Schedule dynamic 5 is on 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ 
% 3.00/1.02  Current options:
% 3.00/1.02  ------ 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options
% 3.00/1.02  
% 3.00/1.02  --out_options                           all
% 3.00/1.02  --tptp_safe_out                         true
% 3.00/1.02  --problem_path                          ""
% 3.00/1.02  --include_path                          ""
% 3.00/1.02  --clausifier                            res/vclausify_rel
% 3.00/1.02  --clausifier_options                    --mode clausify
% 3.00/1.02  --stdin                                 false
% 3.00/1.02  --stats_out                             all
% 3.00/1.02  
% 3.00/1.02  ------ General Options
% 3.00/1.02  
% 3.00/1.02  --fof                                   false
% 3.00/1.02  --time_out_real                         305.
% 3.00/1.02  --time_out_virtual                      -1.
% 3.00/1.02  --symbol_type_check                     false
% 3.00/1.02  --clausify_out                          false
% 3.00/1.02  --sig_cnt_out                           false
% 3.00/1.02  --trig_cnt_out                          false
% 3.00/1.02  --trig_cnt_out_tolerance                1.
% 3.00/1.02  --trig_cnt_out_sk_spl                   false
% 3.00/1.02  --abstr_cl_out                          false
% 3.00/1.02  
% 3.00/1.02  ------ Global Options
% 3.00/1.02  
% 3.00/1.02  --schedule                              default
% 3.00/1.02  --add_important_lit                     false
% 3.00/1.02  --prop_solver_per_cl                    1000
% 3.00/1.02  --min_unsat_core                        false
% 3.00/1.02  --soft_assumptions                      false
% 3.00/1.02  --soft_lemma_size                       3
% 3.00/1.02  --prop_impl_unit_size                   0
% 3.00/1.02  --prop_impl_unit                        []
% 3.00/1.02  --share_sel_clauses                     true
% 3.00/1.02  --reset_solvers                         false
% 3.00/1.02  --bc_imp_inh                            [conj_cone]
% 3.00/1.02  --conj_cone_tolerance                   3.
% 3.00/1.02  --extra_neg_conj                        none
% 3.00/1.02  --large_theory_mode                     true
% 3.00/1.02  --prolific_symb_bound                   200
% 3.00/1.02  --lt_threshold                          2000
% 3.00/1.02  --clause_weak_htbl                      true
% 3.00/1.02  --gc_record_bc_elim                     false
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing Options
% 3.00/1.02  
% 3.00/1.02  --preprocessing_flag                    true
% 3.00/1.02  --time_out_prep_mult                    0.1
% 3.00/1.02  --splitting_mode                        input
% 3.00/1.02  --splitting_grd                         true
% 3.00/1.02  --splitting_cvd                         false
% 3.00/1.02  --splitting_cvd_svl                     false
% 3.00/1.02  --splitting_nvd                         32
% 3.00/1.02  --sub_typing                            true
% 3.00/1.02  --prep_gs_sim                           true
% 3.00/1.02  --prep_unflatten                        true
% 3.00/1.02  --prep_res_sim                          true
% 3.00/1.02  --prep_upred                            true
% 3.00/1.02  --prep_sem_filter                       exhaustive
% 3.00/1.02  --prep_sem_filter_out                   false
% 3.00/1.02  --pred_elim                             true
% 3.00/1.02  --res_sim_input                         true
% 3.00/1.02  --eq_ax_congr_red                       true
% 3.00/1.02  --pure_diseq_elim                       true
% 3.00/1.02  --brand_transform                       false
% 3.00/1.02  --non_eq_to_eq                          false
% 3.00/1.02  --prep_def_merge                        true
% 3.00/1.02  --prep_def_merge_prop_impl              false
% 3.00/1.02  --prep_def_merge_mbd                    true
% 3.00/1.02  --prep_def_merge_tr_red                 false
% 3.00/1.02  --prep_def_merge_tr_cl                  false
% 3.00/1.02  --smt_preprocessing                     true
% 3.00/1.02  --smt_ac_axioms                         fast
% 3.00/1.02  --preprocessed_out                      false
% 3.00/1.02  --preprocessed_stats                    false
% 3.00/1.02  
% 3.00/1.02  ------ Abstraction refinement Options
% 3.00/1.02  
% 3.00/1.02  --abstr_ref                             []
% 3.00/1.02  --abstr_ref_prep                        false
% 3.00/1.02  --abstr_ref_until_sat                   false
% 3.00/1.02  --abstr_ref_sig_restrict                funpre
% 3.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.02  --abstr_ref_under                       []
% 3.00/1.02  
% 3.00/1.02  ------ SAT Options
% 3.00/1.02  
% 3.00/1.02  --sat_mode                              false
% 3.00/1.02  --sat_fm_restart_options                ""
% 3.00/1.02  --sat_gr_def                            false
% 3.00/1.02  --sat_epr_types                         true
% 3.00/1.02  --sat_non_cyclic_types                  false
% 3.00/1.02  --sat_finite_models                     false
% 3.00/1.02  --sat_fm_lemmas                         false
% 3.00/1.02  --sat_fm_prep                           false
% 3.00/1.02  --sat_fm_uc_incr                        true
% 3.00/1.02  --sat_out_model                         small
% 3.00/1.02  --sat_out_clauses                       false
% 3.00/1.02  
% 3.00/1.02  ------ QBF Options
% 3.00/1.02  
% 3.00/1.02  --qbf_mode                              false
% 3.00/1.02  --qbf_elim_univ                         false
% 3.00/1.02  --qbf_dom_inst                          none
% 3.00/1.02  --qbf_dom_pre_inst                      false
% 3.00/1.02  --qbf_sk_in                             false
% 3.00/1.02  --qbf_pred_elim                         true
% 3.00/1.02  --qbf_split                             512
% 3.00/1.02  
% 3.00/1.02  ------ BMC1 Options
% 3.00/1.02  
% 3.00/1.02  --bmc1_incremental                      false
% 3.00/1.02  --bmc1_axioms                           reachable_all
% 3.00/1.02  --bmc1_min_bound                        0
% 3.00/1.02  --bmc1_max_bound                        -1
% 3.00/1.02  --bmc1_max_bound_default                -1
% 3.00/1.02  --bmc1_symbol_reachability              true
% 3.00/1.02  --bmc1_property_lemmas                  false
% 3.00/1.02  --bmc1_k_induction                      false
% 3.00/1.02  --bmc1_non_equiv_states                 false
% 3.00/1.02  --bmc1_deadlock                         false
% 3.00/1.02  --bmc1_ucm                              false
% 3.00/1.02  --bmc1_add_unsat_core                   none
% 3.00/1.02  --bmc1_unsat_core_children              false
% 3.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.02  --bmc1_out_stat                         full
% 3.00/1.02  --bmc1_ground_init                      false
% 3.00/1.02  --bmc1_pre_inst_next_state              false
% 3.00/1.02  --bmc1_pre_inst_state                   false
% 3.00/1.02  --bmc1_pre_inst_reach_state             false
% 3.00/1.02  --bmc1_out_unsat_core                   false
% 3.00/1.02  --bmc1_aig_witness_out                  false
% 3.00/1.02  --bmc1_verbose                          false
% 3.00/1.02  --bmc1_dump_clauses_tptp                false
% 3.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.02  --bmc1_dump_file                        -
% 3.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.02  --bmc1_ucm_extend_mode                  1
% 3.00/1.02  --bmc1_ucm_init_mode                    2
% 3.00/1.02  --bmc1_ucm_cone_mode                    none
% 3.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.02  --bmc1_ucm_relax_model                  4
% 3.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.02  --bmc1_ucm_layered_model                none
% 3.00/1.02  --bmc1_ucm_max_lemma_size               10
% 3.00/1.02  
% 3.00/1.02  ------ AIG Options
% 3.00/1.02  
% 3.00/1.02  --aig_mode                              false
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation Options
% 3.00/1.02  
% 3.00/1.02  --instantiation_flag                    true
% 3.00/1.02  --inst_sos_flag                         false
% 3.00/1.02  --inst_sos_phase                        true
% 3.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel_side                     none
% 3.00/1.02  --inst_solver_per_active                1400
% 3.00/1.02  --inst_solver_calls_frac                1.
% 3.00/1.02  --inst_passive_queue_type               priority_queues
% 3.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.02  --inst_passive_queues_freq              [25;2]
% 3.00/1.02  --inst_dismatching                      true
% 3.00/1.02  --inst_eager_unprocessed_to_passive     true
% 3.00/1.02  --inst_prop_sim_given                   true
% 3.00/1.02  --inst_prop_sim_new                     false
% 3.00/1.02  --inst_subs_new                         false
% 3.00/1.02  --inst_eq_res_simp                      false
% 3.00/1.02  --inst_subs_given                       false
% 3.00/1.02  --inst_orphan_elimination               true
% 3.00/1.02  --inst_learning_loop_flag               true
% 3.00/1.02  --inst_learning_start                   3000
% 3.00/1.02  --inst_learning_factor                  2
% 3.00/1.02  --inst_start_prop_sim_after_learn       3
% 3.00/1.02  --inst_sel_renew                        solver
% 3.00/1.02  --inst_lit_activity_flag                true
% 3.00/1.02  --inst_restr_to_given                   false
% 3.00/1.02  --inst_activity_threshold               500
% 3.00/1.02  --inst_out_proof                        true
% 3.00/1.02  
% 3.00/1.02  ------ Resolution Options
% 3.00/1.02  
% 3.00/1.02  --resolution_flag                       false
% 3.00/1.02  --res_lit_sel                           adaptive
% 3.00/1.02  --res_lit_sel_side                      none
% 3.00/1.02  --res_ordering                          kbo
% 3.00/1.02  --res_to_prop_solver                    active
% 3.00/1.02  --res_prop_simpl_new                    false
% 3.00/1.02  --res_prop_simpl_given                  true
% 3.00/1.02  --res_passive_queue_type                priority_queues
% 3.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.02  --res_passive_queues_freq               [15;5]
% 3.00/1.02  --res_forward_subs                      full
% 3.00/1.02  --res_backward_subs                     full
% 3.00/1.02  --res_forward_subs_resolution           true
% 3.00/1.02  --res_backward_subs_resolution          true
% 3.00/1.02  --res_orphan_elimination                true
% 3.00/1.02  --res_time_limit                        2.
% 3.00/1.02  --res_out_proof                         true
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Options
% 3.00/1.02  
% 3.00/1.02  --superposition_flag                    true
% 3.00/1.02  --sup_passive_queue_type                priority_queues
% 3.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.02  --demod_completeness_check              fast
% 3.00/1.02  --demod_use_ground                      true
% 3.00/1.02  --sup_to_prop_solver                    passive
% 3.00/1.02  --sup_prop_simpl_new                    true
% 3.00/1.02  --sup_prop_simpl_given                  true
% 3.00/1.02  --sup_fun_splitting                     false
% 3.00/1.02  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ Proving...
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS status Theorem for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02   Resolution empty clause
% 3.00/1.02  
% 3.00/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  fof(f15,conjecture,(
% 3.00/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f16,negated_conjecture,(
% 3.00/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.00/1.02    inference(negated_conjecture,[],[f15])).
% 3.00/1.02  
% 3.00/1.02  fof(f31,plain,(
% 3.00/1.02    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.00/1.02    inference(ennf_transformation,[],[f16])).
% 3.00/1.02  
% 3.00/1.02  fof(f32,plain,(
% 3.00/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.00/1.02    inference(flattening,[],[f31])).
% 3.00/1.02  
% 3.00/1.02  fof(f36,plain,(
% 3.00/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f37,plain,(
% 3.00/1.02    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f36])).
% 3.00/1.02  
% 3.00/1.02  fof(f65,plain,(
% 3.00/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f10,axiom,(
% 3.00/1.02    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f24,plain,(
% 3.00/1.02    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f10])).
% 3.00/1.02  
% 3.00/1.02  fof(f51,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f24])).
% 3.00/1.02  
% 3.00/1.02  fof(f1,axiom,(
% 3.00/1.02    v1_xboole_0(k1_xboole_0)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f38,plain,(
% 3.00/1.02    v1_xboole_0(k1_xboole_0)),
% 3.00/1.02    inference(cnf_transformation,[],[f1])).
% 3.00/1.02  
% 3.00/1.02  fof(f13,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f27,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f13])).
% 3.00/1.02  
% 3.00/1.02  fof(f28,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(flattening,[],[f27])).
% 3.00/1.02  
% 3.00/1.02  fof(f35,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(nnf_transformation,[],[f28])).
% 3.00/1.02  
% 3.00/1.02  fof(f54,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f35])).
% 3.00/1.02  
% 3.00/1.02  fof(f64,plain,(
% 3.00/1.02    v1_funct_2(sK2,sK0,sK1)),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f11,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f25,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f11])).
% 3.00/1.02  
% 3.00/1.02  fof(f52,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f25])).
% 3.00/1.02  
% 3.00/1.02  fof(f12,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f26,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f12])).
% 3.00/1.02  
% 3.00/1.02  fof(f53,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f26])).
% 3.00/1.02  
% 3.00/1.02  fof(f67,plain,(
% 3.00/1.02    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f14,axiom,(
% 3.00/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f29,plain,(
% 3.00/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f14])).
% 3.00/1.02  
% 3.00/1.02  fof(f30,plain,(
% 3.00/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/1.02    inference(flattening,[],[f29])).
% 3.00/1.02  
% 3.00/1.02  fof(f61,plain,(
% 3.00/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f30])).
% 3.00/1.02  
% 3.00/1.02  fof(f68,plain,(
% 3.00/1.02    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f9,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f23,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f9])).
% 3.00/1.02  
% 3.00/1.02  fof(f50,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f23])).
% 3.00/1.02  
% 3.00/1.02  fof(f8,axiom,(
% 3.00/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f21,plain,(
% 3.00/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f8])).
% 3.00/1.02  
% 3.00/1.02  fof(f22,plain,(
% 3.00/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/1.02    inference(flattening,[],[f21])).
% 3.00/1.02  
% 3.00/1.02  fof(f49,plain,(
% 3.00/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f22])).
% 3.00/1.02  
% 3.00/1.02  fof(f66,plain,(
% 3.00/1.02    v2_funct_1(sK2)),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f63,plain,(
% 3.00/1.02    v1_funct_1(sK2)),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f48,plain,(
% 3.00/1.02    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f22])).
% 3.00/1.02  
% 3.00/1.02  fof(f7,axiom,(
% 3.00/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f19,plain,(
% 3.00/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f7])).
% 3.00/1.02  
% 3.00/1.02  fof(f20,plain,(
% 3.00/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/1.02    inference(flattening,[],[f19])).
% 3.00/1.02  
% 3.00/1.02  fof(f47,plain,(
% 3.00/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f20])).
% 3.00/1.02  
% 3.00/1.02  fof(f62,plain,(
% 3.00/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f30])).
% 3.00/1.02  
% 3.00/1.02  fof(f46,plain,(
% 3.00/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f20])).
% 3.00/1.02  
% 3.00/1.02  fof(f2,axiom,(
% 3.00/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f18,plain,(
% 3.00/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f2])).
% 3.00/1.02  
% 3.00/1.02  fof(f39,plain,(
% 3.00/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f18])).
% 3.00/1.02  
% 3.00/1.02  fof(f4,axiom,(
% 3.00/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f43,plain,(
% 3.00/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f4])).
% 3.00/1.02  
% 3.00/1.02  fof(f6,axiom,(
% 3.00/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f45,plain,(
% 3.00/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.00/1.02    inference(cnf_transformation,[],[f6])).
% 3.00/1.02  
% 3.00/1.02  fof(f44,plain,(
% 3.00/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.00/1.02    inference(cnf_transformation,[],[f6])).
% 3.00/1.02  
% 3.00/1.02  fof(f3,axiom,(
% 3.00/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f33,plain,(
% 3.00/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.02    inference(nnf_transformation,[],[f3])).
% 3.00/1.02  
% 3.00/1.02  fof(f34,plain,(
% 3.00/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.02    inference(flattening,[],[f33])).
% 3.00/1.02  
% 3.00/1.02  fof(f41,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.00/1.02    inference(cnf_transformation,[],[f34])).
% 3.00/1.02  
% 3.00/1.02  fof(f70,plain,(
% 3.00/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.00/1.02    inference(equality_resolution,[],[f41])).
% 3.00/1.02  
% 3.00/1.02  fof(f57,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f35])).
% 3.00/1.02  
% 3.00/1.02  fof(f74,plain,(
% 3.00/1.02    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.00/1.02    inference(equality_resolution,[],[f57])).
% 3.00/1.02  
% 3.00/1.02  fof(f40,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f34])).
% 3.00/1.02  
% 3.00/1.02  cnf(c_28,negated_conjecture,
% 3.00/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1027,plain,
% 3.00/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_13,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | ~ v1_xboole_0(X2)
% 3.00/1.02      | v1_xboole_0(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1031,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.00/1.02      | v1_xboole_0(X2) != iProver_top
% 3.00/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2903,plain,
% 3.00/1.02      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1027,c_1031]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_33,plain,
% 3.00/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_0,plain,
% 3.00/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_91,plain,
% 3.00/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_592,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.00/1.02      theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1393,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_592]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1394,plain,
% 3.00/1.02      ( sK1 != X0
% 3.00/1.02      | v1_xboole_0(X0) != iProver_top
% 3.00/1.02      | v1_xboole_0(sK1) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1393]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1396,plain,
% 3.00/1.02      ( sK1 != k1_xboole_0
% 3.00/1.02      | v1_xboole_0(sK1) = iProver_top
% 3.00/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1394]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1542,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.02      | ~ v1_xboole_0(X1)
% 3.00/1.02      | v1_xboole_0(sK2) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2148,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/1.02      | ~ v1_xboole_0(sK1)
% 3.00/1.02      | v1_xboole_0(sK2) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1542]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2149,plain,
% 3.00/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.00/1.02      | v1_xboole_0(sK1) != iProver_top
% 3.00/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2148]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_21,plain,
% 3.00/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.02      | k1_xboole_0 = X2 ),
% 3.00/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_29,negated_conjecture,
% 3.00/1.02      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_490,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.02      | sK0 != X1
% 3.00/1.02      | sK1 != X2
% 3.00/1.02      | sK2 != X0
% 3.00/1.02      | k1_xboole_0 = X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_491,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/1.02      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.00/1.02      | k1_xboole_0 = sK1 ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_490]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_493,plain,
% 3.00/1.02      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_491,c_28]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_14,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1030,plain,
% 3.00/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.00/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2504,plain,
% 3.00/1.02      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1027,c_1030]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2535,plain,
% 3.00/1.02      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_493,c_2504]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_15,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1029,plain,
% 3.00/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.00/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2070,plain,
% 3.00/1.02      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1027,c_1029]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_26,negated_conjecture,
% 3.00/1.02      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.00/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2082,plain,
% 3.00/1.02      ( k2_relat_1(sK2) = sK1 ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_2070,c_26]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_23,plain,
% 3.00/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.00/1.02      | ~ v1_relat_1(X0)
% 3.00/1.02      | ~ v1_funct_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_25,negated_conjecture,
% 3.00/1.02      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.00/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.02      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_501,plain,
% 3.00/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.02      | ~ v1_relat_1(X0)
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.02      | k2_funct_1(sK2) != X0
% 3.00/1.02      | k1_relat_1(X0) != sK1
% 3.00/1.02      | k2_relat_1(X0) != sK0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_502,plain,
% 3.00/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.02      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.00/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.02      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.00/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_501]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_12,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_514,plain,
% 3.00/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.02      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.00/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.00/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_502,c_12]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1015,plain,
% 3.00/1.02      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.00/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_10,plain,
% 3.00/1.02      ( ~ v2_funct_1(X0)
% 3.00/1.02      | ~ v1_relat_1(X0)
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_27,negated_conjecture,
% 3.00/1.02      ( v2_funct_1(sK2) ),
% 3.00/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_295,plain,
% 3.00/1.02      ( ~ v1_relat_1(X0)
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.00/1.02      | sK2 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_296,plain,
% 3.00/1.02      ( ~ v1_relat_1(sK2)
% 3.00/1.02      | ~ v1_funct_1(sK2)
% 3.00/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_295]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_30,negated_conjecture,
% 3.00/1.02      ( v1_funct_1(sK2) ),
% 3.00/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_298,plain,
% 3.00/1.02      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_296,c_30]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1024,plain,
% 3.00/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.00/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1280,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/1.02      | v1_relat_1(sK2) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1289,plain,
% 3.00/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_1024,c_30,c_28,c_296,c_1280]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_11,plain,
% 3.00/1.02      ( ~ v2_funct_1(X0)
% 3.00/1.02      | ~ v1_relat_1(X0)
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_281,plain,
% 3.00/1.02      ( ~ v1_relat_1(X0)
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.00/1.02      | sK2 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_282,plain,
% 3.00/1.02      ( ~ v1_relat_1(sK2)
% 3.00/1.02      | ~ v1_funct_1(sK2)
% 3.00/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_281]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_284,plain,
% 3.00/1.02      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_282,c_30]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1025,plain,
% 3.00/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.00/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1293,plain,
% 3.00/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_1025,c_30,c_28,c_282,c_1280]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1336,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != sK0
% 3.00/1.02      | k2_relat_1(sK2) != sK1
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_1015,c_1289,c_1293]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2094,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != sK0
% 3.00/1.02      | sK1 != sK1
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_2082,c_1336]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2098,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != sK0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_2094]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_31,plain,
% 3.00/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1281,plain,
% 3.00/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.00/1.02      | v1_relat_1(sK2) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_8,plain,
% 3.00/1.02      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1372,plain,
% 3.00/1.02      ( ~ v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1373,plain,
% 3.00/1.02      ( v1_relat_1(sK2) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.00/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1372]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2787,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | k1_relat_1(sK2) != sK0 ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_2098,c_31,c_33,c_1281,c_1336,c_1373,c_2082]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2788,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != sK0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_2787]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2793,plain,
% 3.00/1.02      ( sK1 = k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2535,c_2788]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_22,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.00/1.02      | ~ v1_relat_1(X0)
% 3.00/1.02      | ~ v1_funct_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1028,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.00/1.02      | v1_relat_1(X0) != iProver_top
% 3.00/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2228,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.00/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1289,c_1028]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2095,plain,
% 3.00/1.02      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_2082,c_1293]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2240,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.00/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_2228,c_2095]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_9,plain,
% 3.00/1.02      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1375,plain,
% 3.00/1.02      ( v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) | ~ v1_funct_1(sK2) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1376,plain,
% 3.00/1.02      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.00/1.02      | v1_relat_1(sK2) != iProver_top
% 3.00/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2874,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_2240,c_31,c_33,c_1281,c_1373,c_1376]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2879,plain,
% 3.00/1.02      ( sK1 = k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2535,c_2874]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3181,plain,
% 3.00/1.02      ( v1_xboole_0(sK2) = iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_2903,c_33,c_91,c_1396,c_2149,c_2793,c_2879]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1037,plain,
% 3.00/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1036,plain,
% 3.00/1.02      ( X0 = X1
% 3.00/1.02      | v1_xboole_0(X1) != iProver_top
% 3.00/1.02      | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1881,plain,
% 3.00/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1037,c_1036]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3186,plain,
% 3.00/1.02      ( sK2 = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_3181,c_1881]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3199,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))) = iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3186,c_2874]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3220,plain,
% 3.00/1.02      ( k2_relset_1(sK0,sK1,k1_xboole_0) = sK1 ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3186,c_26]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5,plain,
% 3.00/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1035,plain,
% 3.00/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2069,plain,
% 3.00/1.02      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1035,c_1029]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6,plain,
% 3.00/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2085,plain,
% 3.00/1.02      ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_2069,c_6]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3222,plain,
% 3.00/1.02      ( sK1 = k1_xboole_0 ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3220,c_2085]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3290,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_3199,c_3222]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_7,plain,
% 3.00/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3292,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_3290,c_7]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3293,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3292,c_3]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_18,plain,
% 3.00/1.02      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_418,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.00/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.00/1.02      | k2_funct_1(sK2) != X0
% 3.00/1.02      | sK0 != X1
% 3.00/1.02      | sK1 != k1_xboole_0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_419,plain,
% 3.00/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.00/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.00/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.00/1.02      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.02      | sK1 != k1_xboole_0 ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_418]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1019,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.02      | sK1 != k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1194,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.02      | sK1 != k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.00/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_1019,c_3]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1533,plain,
% 3.00/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | sK1 != k1_xboole_0
% 3.00/1.02      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_1194,c_31,c_33,c_1281,c_1373]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1534,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.00/1.02      | sK1 != k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_1533]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3211,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.00/1.02      | sK1 != k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.00/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3186,c_1534]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3257,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 != k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.00/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_3211,c_3222]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3258,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.00/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_3257]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3262,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.00/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3258,c_3]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3295,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.00/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_3293,c_3262]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2905,plain,
% 3.00/1.02      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 3.00/1.02      | v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2874,c_1031]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4,plain,
% 3.00/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = X1
% 3.00/1.02      | k1_xboole_0 = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_86,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_87,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1395,plain,
% 3.00/1.02      ( v1_xboole_0(sK1) | ~ v1_xboole_0(k1_xboole_0) | sK1 != k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1393]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1508,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0)
% 3.00/1.02      | v1_xboole_0(k1_relat_1(sK2))
% 3.00/1.02      | k1_relat_1(sK2) != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_592]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1509,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != X0
% 3.00/1.02      | v1_xboole_0(X0) != iProver_top
% 3.00/1.02      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_1508]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1511,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != k1_xboole_0
% 3.00/1.02      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top
% 3.00/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1509]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_591,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1334,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != X0
% 3.00/1.02      | k1_relat_1(sK2) = k1_xboole_0
% 3.00/1.02      | k1_xboole_0 != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_591]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1558,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != k1_relat_1(X0)
% 3.00/1.02      | k1_relat_1(sK2) = k1_xboole_0
% 3.00/1.02      | k1_xboole_0 != k1_relat_1(X0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1334]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1560,plain,
% 3.00/1.02      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 3.00/1.02      | k1_relat_1(sK2) = k1_xboole_0
% 3.00/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1558]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_597,plain,
% 3.00/1.02      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.00/1.02      theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1559,plain,
% 3.00/1.02      ( k1_relat_1(sK2) = k1_relat_1(X0) | sK2 != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_597]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1561,plain,
% 3.00/1.02      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1559]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1589,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1591,plain,
% 3.00/1.02      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(k1_xboole_0) | sK2 = k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1589]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1903,plain,
% 3.00/1.02      ( k1_relat_1(X0) != X1
% 3.00/1.02      | k1_xboole_0 != X1
% 3.00/1.02      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_591]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1904,plain,
% 3.00/1.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.00/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1903]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4040,plain,
% 3.00/1.02      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_2905,c_28,c_7,c_86,c_87,c_0,c_91,c_1395,c_1511,c_1560,
% 3.00/1.02                 c_1561,c_1591,c_1904,c_2148,c_2793,c_2879]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4044,plain,
% 3.00/1.02      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_4040,c_3186]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4047,plain,
% 3.00/1.02      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_4044,c_1881]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4218,plain,
% 3.00/1.02      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_3295,c_4047]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2502,plain,
% 3.00/1.02      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1035,c_1030]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2524,plain,
% 3.00/1.02      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_2502,c_7]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4219,plain,
% 3.00/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_4218,c_2524]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4220,plain,
% 3.00/1.02      ( $false ),
% 3.00/1.02      inference(equality_resolution_simp,[status(thm)],[c_4219]) ).
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  ------                               Statistics
% 3.00/1.02  
% 3.00/1.02  ------ General
% 3.00/1.02  
% 3.00/1.02  abstr_ref_over_cycles:                  0
% 3.00/1.02  abstr_ref_under_cycles:                 0
% 3.00/1.02  gc_basic_clause_elim:                   0
% 3.00/1.02  forced_gc_time:                         0
% 3.00/1.02  parsing_time:                           0.022
% 3.00/1.02  unif_index_cands_time:                  0.
% 3.00/1.02  unif_index_add_time:                    0.
% 3.00/1.02  orderings_time:                         0.
% 3.00/1.02  out_proof_time:                         0.016
% 3.00/1.02  total_time:                             0.214
% 3.00/1.02  num_of_symbols:                         48
% 3.00/1.02  num_of_terms:                           3730
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing
% 3.00/1.02  
% 3.00/1.02  num_of_splits:                          0
% 3.00/1.02  num_of_split_atoms:                     0
% 3.00/1.02  num_of_reused_defs:                     0
% 3.00/1.02  num_eq_ax_congr_red:                    2
% 3.00/1.02  num_of_sem_filtered_clauses:            1
% 3.00/1.02  num_of_subtypes:                        0
% 3.00/1.02  monotx_restored_types:                  0
% 3.00/1.02  sat_num_of_epr_types:                   0
% 3.00/1.02  sat_num_of_non_cyclic_types:            0
% 3.00/1.02  sat_guarded_non_collapsed_types:        0
% 3.00/1.02  num_pure_diseq_elim:                    0
% 3.00/1.02  simp_replaced_by:                       0
% 3.00/1.02  res_preprocessed:                       119
% 3.00/1.02  prep_upred:                             0
% 3.00/1.02  prep_unflattend:                        43
% 3.00/1.02  smt_new_axioms:                         0
% 3.00/1.02  pred_elim_cands:                        6
% 3.00/1.02  pred_elim:                              2
% 3.00/1.02  pred_elim_cl:                           -1
% 3.00/1.02  pred_elim_cycles:                       3
% 3.00/1.02  merged_defs:                            0
% 3.00/1.02  merged_defs_ncl:                        0
% 3.00/1.02  bin_hyper_res:                          0
% 3.00/1.02  prep_cycles:                            3
% 3.00/1.02  pred_elim_time:                         0.019
% 3.00/1.02  splitting_time:                         0.
% 3.00/1.02  sem_filter_time:                        0.
% 3.00/1.02  monotx_time:                            0.
% 3.00/1.02  subtype_inf_time:                       0.
% 3.00/1.02  
% 3.00/1.02  ------ Problem properties
% 3.00/1.02  
% 3.00/1.02  clauses:                                31
% 3.00/1.02  conjectures:                            3
% 3.00/1.02  epr:                                    3
% 3.00/1.02  horn:                                   26
% 3.00/1.02  ground:                                 16
% 3.00/1.02  unary:                                  9
% 3.00/1.02  binary:                                 6
% 3.00/1.02  lits:                                   81
% 3.00/1.02  lits_eq:                                38
% 3.00/1.02  fd_pure:                                0
% 3.00/1.02  fd_pseudo:                              0
% 3.00/1.02  fd_cond:                                2
% 3.00/1.02  fd_pseudo_cond:                         1
% 3.00/1.02  ac_symbols:                             0
% 3.00/1.02  
% 3.00/1.02  ------ Propositional Solver
% 3.00/1.02  
% 3.00/1.02  prop_solver_calls:                      24
% 3.00/1.02  prop_fast_solver_calls:                 845
% 3.00/1.02  smt_solver_calls:                       0
% 3.00/1.02  smt_fast_solver_calls:                  0
% 3.00/1.02  prop_num_of_clauses:                    1595
% 3.00/1.02  prop_preprocess_simplified:             4732
% 3.00/1.02  prop_fo_subsumed:                       16
% 3.00/1.02  prop_solver_time:                       0.
% 3.00/1.02  smt_solver_time:                        0.
% 3.00/1.02  smt_fast_solver_time:                   0.
% 3.00/1.02  prop_fast_solver_time:                  0.
% 3.00/1.02  prop_unsat_core_time:                   0.
% 3.00/1.02  
% 3.00/1.02  ------ QBF
% 3.00/1.02  
% 3.00/1.02  qbf_q_res:                              0
% 3.00/1.02  qbf_num_tautologies:                    0
% 3.00/1.02  qbf_prep_cycles:                        0
% 3.00/1.02  
% 3.00/1.02  ------ BMC1
% 3.00/1.02  
% 3.00/1.02  bmc1_current_bound:                     -1
% 3.00/1.02  bmc1_last_solved_bound:                 -1
% 3.00/1.02  bmc1_unsat_core_size:                   -1
% 3.00/1.02  bmc1_unsat_core_parents_size:           -1
% 3.00/1.02  bmc1_merge_next_fun:                    0
% 3.00/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation
% 3.00/1.02  
% 3.00/1.02  inst_num_of_clauses:                    732
% 3.00/1.02  inst_num_in_passive:                    47
% 3.00/1.02  inst_num_in_active:                     327
% 3.00/1.02  inst_num_in_unprocessed:                358
% 3.00/1.02  inst_num_of_loops:                      350
% 3.00/1.02  inst_num_of_learning_restarts:          0
% 3.00/1.02  inst_num_moves_active_passive:          20
% 3.00/1.02  inst_lit_activity:                      0
% 3.00/1.02  inst_lit_activity_moves:                0
% 3.00/1.02  inst_num_tautologies:                   0
% 3.00/1.02  inst_num_prop_implied:                  0
% 3.00/1.02  inst_num_existing_simplified:           0
% 3.00/1.02  inst_num_eq_res_simplified:             0
% 3.00/1.02  inst_num_child_elim:                    0
% 3.00/1.02  inst_num_of_dismatching_blockings:      77
% 3.00/1.02  inst_num_of_non_proper_insts:           651
% 3.00/1.02  inst_num_of_duplicates:                 0
% 3.00/1.02  inst_inst_num_from_inst_to_res:         0
% 3.00/1.02  inst_dismatching_checking_time:         0.
% 3.00/1.02  
% 3.00/1.02  ------ Resolution
% 3.00/1.02  
% 3.00/1.02  res_num_of_clauses:                     0
% 3.00/1.02  res_num_in_passive:                     0
% 3.00/1.02  res_num_in_active:                      0
% 3.00/1.02  res_num_of_loops:                       122
% 3.00/1.02  res_forward_subset_subsumed:            22
% 3.00/1.02  res_backward_subset_subsumed:           2
% 3.00/1.02  res_forward_subsumed:                   0
% 3.00/1.02  res_backward_subsumed:                  0
% 3.00/1.02  res_forward_subsumption_resolution:     4
% 3.00/1.02  res_backward_subsumption_resolution:    0
% 3.00/1.02  res_clause_to_clause_subsumption:       162
% 3.00/1.02  res_orphan_elimination:                 0
% 3.00/1.02  res_tautology_del:                      67
% 3.00/1.02  res_num_eq_res_simplified:              0
% 3.00/1.02  res_num_sel_changes:                    0
% 3.00/1.02  res_moves_from_active_to_pass:          0
% 3.00/1.02  
% 3.00/1.02  ------ Superposition
% 3.00/1.02  
% 3.00/1.02  sup_time_total:                         0.
% 3.00/1.02  sup_time_generating:                    0.
% 3.00/1.02  sup_time_sim_full:                      0.
% 3.00/1.02  sup_time_sim_immed:                     0.
% 3.00/1.02  
% 3.00/1.02  sup_num_of_clauses:                     45
% 3.00/1.02  sup_num_in_active:                      33
% 3.00/1.02  sup_num_in_passive:                     12
% 3.00/1.02  sup_num_of_loops:                       68
% 3.00/1.02  sup_fw_superposition:                   44
% 3.00/1.02  sup_bw_superposition:                   27
% 3.00/1.02  sup_immediate_simplified:               73
% 3.00/1.02  sup_given_eliminated:                   2
% 3.00/1.02  comparisons_done:                       0
% 3.00/1.02  comparisons_avoided:                    13
% 3.00/1.02  
% 3.00/1.02  ------ Simplifications
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  sim_fw_subset_subsumed:                 11
% 3.00/1.02  sim_bw_subset_subsumed:                 2
% 3.00/1.02  sim_fw_subsumed:                        21
% 3.00/1.02  sim_bw_subsumed:                        2
% 3.00/1.02  sim_fw_subsumption_res:                 0
% 3.00/1.02  sim_bw_subsumption_res:                 2
% 3.00/1.02  sim_tautology_del:                      3
% 3.00/1.02  sim_eq_tautology_del:                   6
% 3.00/1.02  sim_eq_res_simp:                        2
% 3.00/1.02  sim_fw_demodulated:                     22
% 3.00/1.02  sim_bw_demodulated:                     36
% 3.00/1.02  sim_light_normalised:                   51
% 3.00/1.02  sim_joinable_taut:                      0
% 3.00/1.02  sim_joinable_simp:                      0
% 3.00/1.02  sim_ac_normalised:                      0
% 3.00/1.02  sim_smt_subsumption:                    0
% 3.00/1.02  
%------------------------------------------------------------------------------
