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
% DateTime   : Thu Dec  3 12:02:40 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  211 (17263 expanded)
%              Number of clauses        :  155 (6166 expanded)
%              Number of leaves         :   17 (3177 expanded)
%              Depth                    :   32
%              Number of atoms          :  601 (90082 expanded)
%              Number of equality atoms :  294 (17838 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
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
    inference(ennf_transformation,[],[f12])).

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

fof(f33,plain,(
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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f34,plain,
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

fof(f35,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f34])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_493,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_495,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_24])).

cnf(c_593,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_605,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1082,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | k1_relset_1(X1_45,X2_45,X0_45) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1079,plain,
    ( k1_relset_1(X0_45,X1_45,X2_45) = k1_relat_1(X2_45)
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_1834,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1082,c_1079])).

cnf(c_2043,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_593,c_1834])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_297,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_298,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_300,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_26])).

cnf(c_602,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_300])).

cnf(c_1085,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1307,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1338,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1085,c_24,c_602,c_1307])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_607,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_45),k2_relat_1(X0_45))))
    | ~ v1_relat_1(X0_45)
    | ~ v1_funct_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1081,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_45),k2_relat_1(X0_45)))) = iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_funct_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_2319,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1081])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | k2_relset_1(X1_45,X2_45,X0_45) = k2_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1080,plain,
    ( k2_relset_1(X0_45,X1_45,X2_45) = k2_relat_1(X2_45)
    | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_1844,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1082,c_1080])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_606,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1849,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1844,c_606])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_283,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_284,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_286,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_26])).

cnf(c_603,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_286])).

cnf(c_1084,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_1334,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1084,c_24,c_603,c_1307])).

cnf(c_1935,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1849,c_1334])).

cnf(c_2356,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2319,c_1935])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1308,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_613,plain,
    ( ~ v1_relat_1(X0_45)
    | v1_relat_1(k2_funct_1(X0_45))
    | ~ v1_funct_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1433,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_1434,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_614,plain,
    ( ~ v1_relat_1(X0_45)
    | ~ v1_funct_1(X0_45)
    | v1_funct_1(k2_funct_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1449,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_1450,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_2575,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2356,c_27,c_29,c_1308,c_1434,c_1450])).

cnf(c_2585,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2575,c_1079])).

cnf(c_2587,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2585,c_1935])).

cnf(c_2665,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2043,c_2587])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_503,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0
    | k2_funct_1(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_504,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_516,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_504,c_7])).

cnf(c_592,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_1094,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_682,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1665,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_27,c_29,c_682,c_1308,c_1450])).

cnf(c_1666,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1665])).

cnf(c_1669,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1666,c_1334,c_1338])).

cnf(c_1934,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1849,c_1669])).

cnf(c_1938,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1934])).

cnf(c_2169,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_1938])).

cnf(c_2580,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_2575])).

cnf(c_2759,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2665,c_2169,c_2580])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ v1_xboole_0(X2_45)
    | v1_xboole_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1078,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
    | v1_xboole_0(X2_45) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_2228,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1078])).

cnf(c_2768,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2759,c_2228])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_86,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_623,plain,
    ( ~ v1_xboole_0(X0_45)
    | v1_xboole_0(X1_45)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1428,plain,
    ( ~ v1_xboole_0(X0_45)
    | v1_xboole_0(sK1)
    | sK1 != X0_45 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1429,plain,
    ( sK1 != X0_45
    | v1_xboole_0(X0_45) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_1431,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_1575,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ v1_xboole_0(X1_45)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_2096,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_2097,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2096])).

cnf(c_3327,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2768,c_29,c_86,c_1431,c_2097,c_2169,c_2580])).

cnf(c_617,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1071,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_616,plain,
    ( ~ v1_xboole_0(X0_45)
    | ~ v1_xboole_0(X1_45)
    | X1_45 = X0_45 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1072,plain,
    ( X0_45 = X1_45
    | v1_xboole_0(X1_45) != iProver_top
    | v1_xboole_0(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_1467,plain,
    ( k1_xboole_0 = X0_45
    | v1_xboole_0(X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1072])).

cnf(c_3332,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3327,c_1467])).

cnf(c_3541,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3332,c_1338])).

cnf(c_3767,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)))) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3541,c_1081])).

cnf(c_74,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_76,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_1312,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_615,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1311,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_1314,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_627,plain,
    ( ~ v1_funct_1(X0_45)
    | v1_funct_1(X1_45)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1328,plain,
    ( v1_funct_1(X0_45)
    | ~ v1_funct_1(sK2)
    | X0_45 != sK2 ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_1329,plain,
    ( X0_45 != sK2
    | v1_funct_1(X0_45) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_1331,plain,
    ( k1_xboole_0 != sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_1385,plain,
    ( ~ v1_xboole_0(X0_45)
    | ~ v1_xboole_0(sK2)
    | X0_45 = sK2 ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_1387,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_1430,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_1488,plain,
    ( v1_funct_1(X0_45)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | X0_45 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_1644,plain,
    ( v1_funct_1(k2_funct_1(X0_45))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(X0_45) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_1646,plain,
    ( k2_funct_1(X0_45) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(X0_45)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_1648,plain,
    ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_626,plain,
    ( X0_45 != X1_45
    | k2_funct_1(X0_45) = k2_funct_1(X1_45) ),
    theory(equality)).

cnf(c_1645,plain,
    ( X0_45 != sK2
    | k2_funct_1(X0_45) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_1650,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1645])).

cnf(c_3903,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3767,c_27,c_24,c_29,c_76,c_0,c_1308,c_1312,c_1314,c_1331,c_1387,c_1430,c_1450,c_1648,c_1650,c_2096,c_2169,c_2580])).

cnf(c_3908,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3903,c_1078])).

cnf(c_2771,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2759,c_1935])).

cnf(c_3532,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3332,c_2771])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
    | ~ v1_xboole_0(X1_45)
    | v1_xboole_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1077,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
    | v1_xboole_0(X1_45) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_2321,plain,
    ( v1_relat_1(X0_45) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_xboole_0(X0_45) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1077])).

cnf(c_3931,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3532,c_2321])).

cnf(c_4124,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3908,c_27,c_24,c_29,c_76,c_0,c_86,c_1308,c_1312,c_1314,c_1331,c_1387,c_1430,c_1450,c_1648,c_1650,c_2096,c_2169,c_2580,c_3931])).

cnf(c_4129,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4124,c_1467])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_421,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1090,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_676,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_1560,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1090,c_27,c_29,c_676,c_1308,c_1450])).

cnf(c_1561,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1560])).

cnf(c_2775,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2759,c_1561])).

cnf(c_2806,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2775])).

cnf(c_4223,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2806,c_3332])).

cnf(c_5019,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4129,c_4223])).

cnf(c_1073,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_1835,plain,
    ( k1_relset_1(X0_45,X1_45,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1073,c_1079])).

cnf(c_5034,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5019,c_1835])).

cnf(c_5023,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4129,c_3541])).

cnf(c_2772,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2759,c_1849])).

cnf(c_3535,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3332,c_2772])).

cnf(c_5025,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5023,c_3535])).

cnf(c_5943,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5034,c_5025])).

cnf(c_5948,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5943,c_1073])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.88/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.03  
% 2.88/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/1.03  
% 2.88/1.03  ------  iProver source info
% 2.88/1.03  
% 2.88/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.88/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/1.03  git: non_committed_changes: false
% 2.88/1.03  git: last_make_outside_of_git: false
% 2.88/1.03  
% 2.88/1.03  ------ 
% 2.88/1.03  
% 2.88/1.03  ------ Input Options
% 2.88/1.03  
% 2.88/1.03  --out_options                           all
% 2.88/1.03  --tptp_safe_out                         true
% 2.88/1.03  --problem_path                          ""
% 2.88/1.03  --include_path                          ""
% 2.88/1.03  --clausifier                            res/vclausify_rel
% 2.88/1.03  --clausifier_options                    --mode clausify
% 2.88/1.03  --stdin                                 false
% 2.88/1.03  --stats_out                             all
% 2.88/1.03  
% 2.88/1.03  ------ General Options
% 2.88/1.03  
% 2.88/1.03  --fof                                   false
% 2.88/1.03  --time_out_real                         305.
% 2.88/1.03  --time_out_virtual                      -1.
% 2.88/1.03  --symbol_type_check                     false
% 2.88/1.03  --clausify_out                          false
% 2.88/1.03  --sig_cnt_out                           false
% 2.88/1.03  --trig_cnt_out                          false
% 2.88/1.03  --trig_cnt_out_tolerance                1.
% 2.88/1.03  --trig_cnt_out_sk_spl                   false
% 2.88/1.03  --abstr_cl_out                          false
% 2.88/1.03  
% 2.88/1.03  ------ Global Options
% 2.88/1.03  
% 2.88/1.03  --schedule                              default
% 2.88/1.03  --add_important_lit                     false
% 2.88/1.03  --prop_solver_per_cl                    1000
% 2.88/1.03  --min_unsat_core                        false
% 2.88/1.03  --soft_assumptions                      false
% 2.88/1.03  --soft_lemma_size                       3
% 2.88/1.03  --prop_impl_unit_size                   0
% 2.88/1.03  --prop_impl_unit                        []
% 2.88/1.03  --share_sel_clauses                     true
% 2.88/1.03  --reset_solvers                         false
% 2.88/1.03  --bc_imp_inh                            [conj_cone]
% 2.88/1.03  --conj_cone_tolerance                   3.
% 2.88/1.03  --extra_neg_conj                        none
% 2.88/1.03  --large_theory_mode                     true
% 2.88/1.03  --prolific_symb_bound                   200
% 2.88/1.03  --lt_threshold                          2000
% 2.88/1.03  --clause_weak_htbl                      true
% 2.88/1.03  --gc_record_bc_elim                     false
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing Options
% 2.88/1.03  
% 2.88/1.03  --preprocessing_flag                    true
% 2.88/1.03  --time_out_prep_mult                    0.1
% 2.88/1.03  --splitting_mode                        input
% 2.88/1.03  --splitting_grd                         true
% 2.88/1.03  --splitting_cvd                         false
% 2.88/1.03  --splitting_cvd_svl                     false
% 2.88/1.03  --splitting_nvd                         32
% 2.88/1.03  --sub_typing                            true
% 2.88/1.03  --prep_gs_sim                           true
% 2.88/1.03  --prep_unflatten                        true
% 2.88/1.03  --prep_res_sim                          true
% 2.88/1.03  --prep_upred                            true
% 2.88/1.03  --prep_sem_filter                       exhaustive
% 2.88/1.03  --prep_sem_filter_out                   false
% 2.88/1.03  --pred_elim                             true
% 2.88/1.03  --res_sim_input                         true
% 2.88/1.03  --eq_ax_congr_red                       true
% 2.88/1.03  --pure_diseq_elim                       true
% 2.88/1.03  --brand_transform                       false
% 2.88/1.03  --non_eq_to_eq                          false
% 2.88/1.03  --prep_def_merge                        true
% 2.88/1.03  --prep_def_merge_prop_impl              false
% 2.88/1.03  --prep_def_merge_mbd                    true
% 2.88/1.03  --prep_def_merge_tr_red                 false
% 2.88/1.03  --prep_def_merge_tr_cl                  false
% 2.88/1.03  --smt_preprocessing                     true
% 2.88/1.03  --smt_ac_axioms                         fast
% 2.88/1.03  --preprocessed_out                      false
% 2.88/1.03  --preprocessed_stats                    false
% 2.88/1.03  
% 2.88/1.03  ------ Abstraction refinement Options
% 2.88/1.03  
% 2.88/1.03  --abstr_ref                             []
% 2.88/1.03  --abstr_ref_prep                        false
% 2.88/1.03  --abstr_ref_until_sat                   false
% 2.88/1.03  --abstr_ref_sig_restrict                funpre
% 2.88/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/1.03  --abstr_ref_under                       []
% 2.88/1.03  
% 2.88/1.03  ------ SAT Options
% 2.88/1.03  
% 2.88/1.03  --sat_mode                              false
% 2.88/1.03  --sat_fm_restart_options                ""
% 2.88/1.03  --sat_gr_def                            false
% 2.88/1.03  --sat_epr_types                         true
% 2.88/1.03  --sat_non_cyclic_types                  false
% 2.88/1.03  --sat_finite_models                     false
% 2.88/1.03  --sat_fm_lemmas                         false
% 2.88/1.03  --sat_fm_prep                           false
% 2.88/1.03  --sat_fm_uc_incr                        true
% 2.88/1.03  --sat_out_model                         small
% 2.88/1.03  --sat_out_clauses                       false
% 2.88/1.03  
% 2.88/1.03  ------ QBF Options
% 2.88/1.03  
% 2.88/1.03  --qbf_mode                              false
% 2.88/1.03  --qbf_elim_univ                         false
% 2.88/1.03  --qbf_dom_inst                          none
% 2.88/1.03  --qbf_dom_pre_inst                      false
% 2.88/1.03  --qbf_sk_in                             false
% 2.88/1.03  --qbf_pred_elim                         true
% 2.88/1.03  --qbf_split                             512
% 2.88/1.03  
% 2.88/1.03  ------ BMC1 Options
% 2.88/1.03  
% 2.88/1.03  --bmc1_incremental                      false
% 2.88/1.03  --bmc1_axioms                           reachable_all
% 2.88/1.03  --bmc1_min_bound                        0
% 2.88/1.03  --bmc1_max_bound                        -1
% 2.88/1.03  --bmc1_max_bound_default                -1
% 2.88/1.03  --bmc1_symbol_reachability              true
% 2.88/1.03  --bmc1_property_lemmas                  false
% 2.88/1.03  --bmc1_k_induction                      false
% 2.88/1.03  --bmc1_non_equiv_states                 false
% 2.88/1.03  --bmc1_deadlock                         false
% 2.88/1.03  --bmc1_ucm                              false
% 2.88/1.03  --bmc1_add_unsat_core                   none
% 2.88/1.03  --bmc1_unsat_core_children              false
% 2.88/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/1.03  --bmc1_out_stat                         full
% 2.88/1.03  --bmc1_ground_init                      false
% 2.88/1.03  --bmc1_pre_inst_next_state              false
% 2.88/1.03  --bmc1_pre_inst_state                   false
% 2.88/1.03  --bmc1_pre_inst_reach_state             false
% 2.88/1.03  --bmc1_out_unsat_core                   false
% 2.88/1.03  --bmc1_aig_witness_out                  false
% 2.88/1.03  --bmc1_verbose                          false
% 2.88/1.03  --bmc1_dump_clauses_tptp                false
% 2.88/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.88/1.03  --bmc1_dump_file                        -
% 2.88/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.88/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.88/1.03  --bmc1_ucm_extend_mode                  1
% 2.88/1.03  --bmc1_ucm_init_mode                    2
% 2.88/1.03  --bmc1_ucm_cone_mode                    none
% 2.88/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.88/1.03  --bmc1_ucm_relax_model                  4
% 2.88/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.88/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/1.03  --bmc1_ucm_layered_model                none
% 2.88/1.03  --bmc1_ucm_max_lemma_size               10
% 2.88/1.03  
% 2.88/1.03  ------ AIG Options
% 2.88/1.03  
% 2.88/1.03  --aig_mode                              false
% 2.88/1.03  
% 2.88/1.03  ------ Instantiation Options
% 2.88/1.03  
% 2.88/1.03  --instantiation_flag                    true
% 2.88/1.03  --inst_sos_flag                         false
% 2.88/1.03  --inst_sos_phase                        true
% 2.88/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel_side                     num_symb
% 2.88/1.03  --inst_solver_per_active                1400
% 2.88/1.03  --inst_solver_calls_frac                1.
% 2.88/1.03  --inst_passive_queue_type               priority_queues
% 2.88/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/1.03  --inst_passive_queues_freq              [25;2]
% 2.88/1.03  --inst_dismatching                      true
% 2.88/1.03  --inst_eager_unprocessed_to_passive     true
% 2.88/1.03  --inst_prop_sim_given                   true
% 2.88/1.03  --inst_prop_sim_new                     false
% 2.88/1.03  --inst_subs_new                         false
% 2.88/1.03  --inst_eq_res_simp                      false
% 2.88/1.03  --inst_subs_given                       false
% 2.88/1.03  --inst_orphan_elimination               true
% 2.88/1.03  --inst_learning_loop_flag               true
% 2.88/1.03  --inst_learning_start                   3000
% 2.88/1.03  --inst_learning_factor                  2
% 2.88/1.03  --inst_start_prop_sim_after_learn       3
% 2.88/1.03  --inst_sel_renew                        solver
% 2.88/1.03  --inst_lit_activity_flag                true
% 2.88/1.03  --inst_restr_to_given                   false
% 2.88/1.03  --inst_activity_threshold               500
% 2.88/1.03  --inst_out_proof                        true
% 2.88/1.03  
% 2.88/1.03  ------ Resolution Options
% 2.88/1.03  
% 2.88/1.03  --resolution_flag                       true
% 2.88/1.03  --res_lit_sel                           adaptive
% 2.88/1.03  --res_lit_sel_side                      none
% 2.88/1.03  --res_ordering                          kbo
% 2.88/1.03  --res_to_prop_solver                    active
% 2.88/1.03  --res_prop_simpl_new                    false
% 2.88/1.03  --res_prop_simpl_given                  true
% 2.88/1.03  --res_passive_queue_type                priority_queues
% 2.88/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/1.03  --res_passive_queues_freq               [15;5]
% 2.88/1.03  --res_forward_subs                      full
% 2.88/1.03  --res_backward_subs                     full
% 2.88/1.03  --res_forward_subs_resolution           true
% 2.88/1.03  --res_backward_subs_resolution          true
% 2.88/1.03  --res_orphan_elimination                true
% 2.88/1.03  --res_time_limit                        2.
% 2.88/1.03  --res_out_proof                         true
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Options
% 2.88/1.03  
% 2.88/1.03  --superposition_flag                    true
% 2.88/1.03  --sup_passive_queue_type                priority_queues
% 2.88/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.88/1.03  --demod_completeness_check              fast
% 2.88/1.03  --demod_use_ground                      true
% 2.88/1.03  --sup_to_prop_solver                    passive
% 2.88/1.03  --sup_prop_simpl_new                    true
% 2.88/1.03  --sup_prop_simpl_given                  true
% 2.88/1.03  --sup_fun_splitting                     false
% 2.88/1.03  --sup_smt_interval                      50000
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Simplification Setup
% 2.88/1.03  
% 2.88/1.03  --sup_indices_passive                   []
% 2.88/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_full_bw                           [BwDemod]
% 2.88/1.03  --sup_immed_triv                        [TrivRules]
% 2.88/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_immed_bw_main                     []
% 2.88/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  
% 2.88/1.03  ------ Combination Options
% 2.88/1.03  
% 2.88/1.03  --comb_res_mult                         3
% 2.88/1.03  --comb_sup_mult                         2
% 2.88/1.03  --comb_inst_mult                        10
% 2.88/1.03  
% 2.88/1.03  ------ Debug Options
% 2.88/1.03  
% 2.88/1.03  --dbg_backtrace                         false
% 2.88/1.03  --dbg_dump_prop_clauses                 false
% 2.88/1.03  --dbg_dump_prop_clauses_file            -
% 2.88/1.03  --dbg_out_stat                          false
% 2.88/1.03  ------ Parsing...
% 2.88/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/1.03  ------ Proving...
% 2.88/1.03  ------ Problem Properties 
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  clauses                                 27
% 2.88/1.03  conjectures                             3
% 2.88/1.03  EPR                                     3
% 2.88/1.03  Horn                                    23
% 2.88/1.03  unary                                   5
% 2.88/1.03  binary                                  6
% 2.88/1.03  lits                                    77
% 2.88/1.03  lits eq                                 31
% 2.88/1.03  fd_pure                                 0
% 2.88/1.03  fd_pseudo                               0
% 2.88/1.03  fd_cond                                 1
% 2.88/1.03  fd_pseudo_cond                          1
% 2.88/1.03  AC symbols                              0
% 2.88/1.03  
% 2.88/1.03  ------ Schedule dynamic 5 is on 
% 2.88/1.03  
% 2.88/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  ------ 
% 2.88/1.03  Current options:
% 2.88/1.03  ------ 
% 2.88/1.03  
% 2.88/1.03  ------ Input Options
% 2.88/1.03  
% 2.88/1.03  --out_options                           all
% 2.88/1.03  --tptp_safe_out                         true
% 2.88/1.03  --problem_path                          ""
% 2.88/1.03  --include_path                          ""
% 2.88/1.03  --clausifier                            res/vclausify_rel
% 2.88/1.03  --clausifier_options                    --mode clausify
% 2.88/1.03  --stdin                                 false
% 2.88/1.03  --stats_out                             all
% 2.88/1.03  
% 2.88/1.03  ------ General Options
% 2.88/1.03  
% 2.88/1.03  --fof                                   false
% 2.88/1.03  --time_out_real                         305.
% 2.88/1.03  --time_out_virtual                      -1.
% 2.88/1.03  --symbol_type_check                     false
% 2.88/1.03  --clausify_out                          false
% 2.88/1.03  --sig_cnt_out                           false
% 2.88/1.03  --trig_cnt_out                          false
% 2.88/1.03  --trig_cnt_out_tolerance                1.
% 2.88/1.03  --trig_cnt_out_sk_spl                   false
% 2.88/1.03  --abstr_cl_out                          false
% 2.88/1.03  
% 2.88/1.03  ------ Global Options
% 2.88/1.03  
% 2.88/1.03  --schedule                              default
% 2.88/1.03  --add_important_lit                     false
% 2.88/1.03  --prop_solver_per_cl                    1000
% 2.88/1.03  --min_unsat_core                        false
% 2.88/1.03  --soft_assumptions                      false
% 2.88/1.03  --soft_lemma_size                       3
% 2.88/1.03  --prop_impl_unit_size                   0
% 2.88/1.03  --prop_impl_unit                        []
% 2.88/1.03  --share_sel_clauses                     true
% 2.88/1.03  --reset_solvers                         false
% 2.88/1.03  --bc_imp_inh                            [conj_cone]
% 2.88/1.03  --conj_cone_tolerance                   3.
% 2.88/1.03  --extra_neg_conj                        none
% 2.88/1.03  --large_theory_mode                     true
% 2.88/1.03  --prolific_symb_bound                   200
% 2.88/1.03  --lt_threshold                          2000
% 2.88/1.03  --clause_weak_htbl                      true
% 2.88/1.03  --gc_record_bc_elim                     false
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing Options
% 2.88/1.03  
% 2.88/1.03  --preprocessing_flag                    true
% 2.88/1.03  --time_out_prep_mult                    0.1
% 2.88/1.03  --splitting_mode                        input
% 2.88/1.03  --splitting_grd                         true
% 2.88/1.03  --splitting_cvd                         false
% 2.88/1.03  --splitting_cvd_svl                     false
% 2.88/1.03  --splitting_nvd                         32
% 2.88/1.03  --sub_typing                            true
% 2.88/1.03  --prep_gs_sim                           true
% 2.88/1.03  --prep_unflatten                        true
% 2.88/1.03  --prep_res_sim                          true
% 2.88/1.03  --prep_upred                            true
% 2.88/1.03  --prep_sem_filter                       exhaustive
% 2.88/1.03  --prep_sem_filter_out                   false
% 2.88/1.03  --pred_elim                             true
% 2.88/1.03  --res_sim_input                         true
% 2.88/1.03  --eq_ax_congr_red                       true
% 2.88/1.03  --pure_diseq_elim                       true
% 2.88/1.03  --brand_transform                       false
% 2.88/1.03  --non_eq_to_eq                          false
% 2.88/1.03  --prep_def_merge                        true
% 2.88/1.03  --prep_def_merge_prop_impl              false
% 2.88/1.03  --prep_def_merge_mbd                    true
% 2.88/1.03  --prep_def_merge_tr_red                 false
% 2.88/1.03  --prep_def_merge_tr_cl                  false
% 2.88/1.03  --smt_preprocessing                     true
% 2.88/1.03  --smt_ac_axioms                         fast
% 2.88/1.03  --preprocessed_out                      false
% 2.88/1.03  --preprocessed_stats                    false
% 2.88/1.03  
% 2.88/1.03  ------ Abstraction refinement Options
% 2.88/1.03  
% 2.88/1.03  --abstr_ref                             []
% 2.88/1.03  --abstr_ref_prep                        false
% 2.88/1.03  --abstr_ref_until_sat                   false
% 2.88/1.03  --abstr_ref_sig_restrict                funpre
% 2.88/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/1.03  --abstr_ref_under                       []
% 2.88/1.03  
% 2.88/1.03  ------ SAT Options
% 2.88/1.03  
% 2.88/1.03  --sat_mode                              false
% 2.88/1.03  --sat_fm_restart_options                ""
% 2.88/1.03  --sat_gr_def                            false
% 2.88/1.03  --sat_epr_types                         true
% 2.88/1.03  --sat_non_cyclic_types                  false
% 2.88/1.03  --sat_finite_models                     false
% 2.88/1.03  --sat_fm_lemmas                         false
% 2.88/1.03  --sat_fm_prep                           false
% 2.88/1.03  --sat_fm_uc_incr                        true
% 2.88/1.03  --sat_out_model                         small
% 2.88/1.03  --sat_out_clauses                       false
% 2.88/1.03  
% 2.88/1.03  ------ QBF Options
% 2.88/1.03  
% 2.88/1.03  --qbf_mode                              false
% 2.88/1.03  --qbf_elim_univ                         false
% 2.88/1.03  --qbf_dom_inst                          none
% 2.88/1.03  --qbf_dom_pre_inst                      false
% 2.88/1.03  --qbf_sk_in                             false
% 2.88/1.03  --qbf_pred_elim                         true
% 2.88/1.03  --qbf_split                             512
% 2.88/1.03  
% 2.88/1.03  ------ BMC1 Options
% 2.88/1.03  
% 2.88/1.03  --bmc1_incremental                      false
% 2.88/1.03  --bmc1_axioms                           reachable_all
% 2.88/1.03  --bmc1_min_bound                        0
% 2.88/1.03  --bmc1_max_bound                        -1
% 2.88/1.03  --bmc1_max_bound_default                -1
% 2.88/1.03  --bmc1_symbol_reachability              true
% 2.88/1.03  --bmc1_property_lemmas                  false
% 2.88/1.03  --bmc1_k_induction                      false
% 2.88/1.03  --bmc1_non_equiv_states                 false
% 2.88/1.03  --bmc1_deadlock                         false
% 2.88/1.03  --bmc1_ucm                              false
% 2.88/1.03  --bmc1_add_unsat_core                   none
% 2.88/1.03  --bmc1_unsat_core_children              false
% 2.88/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/1.03  --bmc1_out_stat                         full
% 2.88/1.03  --bmc1_ground_init                      false
% 2.88/1.03  --bmc1_pre_inst_next_state              false
% 2.88/1.03  --bmc1_pre_inst_state                   false
% 2.88/1.03  --bmc1_pre_inst_reach_state             false
% 2.88/1.03  --bmc1_out_unsat_core                   false
% 2.88/1.03  --bmc1_aig_witness_out                  false
% 2.88/1.03  --bmc1_verbose                          false
% 2.88/1.03  --bmc1_dump_clauses_tptp                false
% 2.88/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.88/1.03  --bmc1_dump_file                        -
% 2.88/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.88/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.88/1.03  --bmc1_ucm_extend_mode                  1
% 2.88/1.03  --bmc1_ucm_init_mode                    2
% 2.88/1.03  --bmc1_ucm_cone_mode                    none
% 2.88/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.88/1.03  --bmc1_ucm_relax_model                  4
% 2.88/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.88/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/1.03  --bmc1_ucm_layered_model                none
% 2.88/1.03  --bmc1_ucm_max_lemma_size               10
% 2.88/1.03  
% 2.88/1.03  ------ AIG Options
% 2.88/1.03  
% 2.88/1.03  --aig_mode                              false
% 2.88/1.03  
% 2.88/1.03  ------ Instantiation Options
% 2.88/1.03  
% 2.88/1.03  --instantiation_flag                    true
% 2.88/1.03  --inst_sos_flag                         false
% 2.88/1.03  --inst_sos_phase                        true
% 2.88/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/1.03  --inst_lit_sel_side                     none
% 2.88/1.03  --inst_solver_per_active                1400
% 2.88/1.03  --inst_solver_calls_frac                1.
% 2.88/1.03  --inst_passive_queue_type               priority_queues
% 2.88/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/1.03  --inst_passive_queues_freq              [25;2]
% 2.88/1.03  --inst_dismatching                      true
% 2.88/1.03  --inst_eager_unprocessed_to_passive     true
% 2.88/1.03  --inst_prop_sim_given                   true
% 2.88/1.03  --inst_prop_sim_new                     false
% 2.88/1.03  --inst_subs_new                         false
% 2.88/1.03  --inst_eq_res_simp                      false
% 2.88/1.03  --inst_subs_given                       false
% 2.88/1.03  --inst_orphan_elimination               true
% 2.88/1.03  --inst_learning_loop_flag               true
% 2.88/1.03  --inst_learning_start                   3000
% 2.88/1.03  --inst_learning_factor                  2
% 2.88/1.03  --inst_start_prop_sim_after_learn       3
% 2.88/1.03  --inst_sel_renew                        solver
% 2.88/1.03  --inst_lit_activity_flag                true
% 2.88/1.03  --inst_restr_to_given                   false
% 2.88/1.03  --inst_activity_threshold               500
% 2.88/1.03  --inst_out_proof                        true
% 2.88/1.03  
% 2.88/1.03  ------ Resolution Options
% 2.88/1.03  
% 2.88/1.03  --resolution_flag                       false
% 2.88/1.03  --res_lit_sel                           adaptive
% 2.88/1.03  --res_lit_sel_side                      none
% 2.88/1.03  --res_ordering                          kbo
% 2.88/1.03  --res_to_prop_solver                    active
% 2.88/1.03  --res_prop_simpl_new                    false
% 2.88/1.03  --res_prop_simpl_given                  true
% 2.88/1.03  --res_passive_queue_type                priority_queues
% 2.88/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/1.03  --res_passive_queues_freq               [15;5]
% 2.88/1.03  --res_forward_subs                      full
% 2.88/1.03  --res_backward_subs                     full
% 2.88/1.03  --res_forward_subs_resolution           true
% 2.88/1.03  --res_backward_subs_resolution          true
% 2.88/1.03  --res_orphan_elimination                true
% 2.88/1.03  --res_time_limit                        2.
% 2.88/1.03  --res_out_proof                         true
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Options
% 2.88/1.03  
% 2.88/1.03  --superposition_flag                    true
% 2.88/1.03  --sup_passive_queue_type                priority_queues
% 2.88/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.88/1.03  --demod_completeness_check              fast
% 2.88/1.03  --demod_use_ground                      true
% 2.88/1.03  --sup_to_prop_solver                    passive
% 2.88/1.03  --sup_prop_simpl_new                    true
% 2.88/1.03  --sup_prop_simpl_given                  true
% 2.88/1.03  --sup_fun_splitting                     false
% 2.88/1.03  --sup_smt_interval                      50000
% 2.88/1.03  
% 2.88/1.03  ------ Superposition Simplification Setup
% 2.88/1.03  
% 2.88/1.03  --sup_indices_passive                   []
% 2.88/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_full_bw                           [BwDemod]
% 2.88/1.03  --sup_immed_triv                        [TrivRules]
% 2.88/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_immed_bw_main                     []
% 2.88/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.03  
% 2.88/1.03  ------ Combination Options
% 2.88/1.03  
% 2.88/1.03  --comb_res_mult                         3
% 2.88/1.03  --comb_sup_mult                         2
% 2.88/1.03  --comb_inst_mult                        10
% 2.88/1.03  
% 2.88/1.03  ------ Debug Options
% 2.88/1.03  
% 2.88/1.03  --dbg_backtrace                         false
% 2.88/1.03  --dbg_dump_prop_clauses                 false
% 2.88/1.03  --dbg_dump_prop_clauses_file            -
% 2.88/1.03  --dbg_out_stat                          false
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  ------ Proving...
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  % SZS status Theorem for theBenchmark.p
% 2.88/1.03  
% 2.88/1.03   Resolution empty clause
% 2.88/1.03  
% 2.88/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/1.03  
% 2.88/1.03  fof(f12,axiom,(
% 2.88/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f27,plain,(
% 2.88/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.03    inference(ennf_transformation,[],[f12])).
% 2.88/1.03  
% 2.88/1.03  fof(f28,plain,(
% 2.88/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.03    inference(flattening,[],[f27])).
% 2.88/1.03  
% 2.88/1.03  fof(f33,plain,(
% 2.88/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.03    inference(nnf_transformation,[],[f28])).
% 2.88/1.03  
% 2.88/1.03  fof(f48,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.03    inference(cnf_transformation,[],[f33])).
% 2.88/1.03  
% 2.88/1.03  fof(f14,conjecture,(
% 2.88/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f15,negated_conjecture,(
% 2.88/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.88/1.03    inference(negated_conjecture,[],[f14])).
% 2.88/1.03  
% 2.88/1.03  fof(f31,plain,(
% 2.88/1.03    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.88/1.03    inference(ennf_transformation,[],[f15])).
% 2.88/1.03  
% 2.88/1.03  fof(f32,plain,(
% 2.88/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.88/1.03    inference(flattening,[],[f31])).
% 2.88/1.03  
% 2.88/1.03  fof(f34,plain,(
% 2.88/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.88/1.03    introduced(choice_axiom,[])).
% 2.88/1.03  
% 2.88/1.03  fof(f35,plain,(
% 2.88/1.03    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.88/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f34])).
% 2.88/1.03  
% 2.88/1.03  fof(f58,plain,(
% 2.88/1.03    v1_funct_2(sK2,sK0,sK1)),
% 2.88/1.03    inference(cnf_transformation,[],[f35])).
% 2.88/1.03  
% 2.88/1.03  fof(f59,plain,(
% 2.88/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.88/1.03    inference(cnf_transformation,[],[f35])).
% 2.88/1.03  
% 2.88/1.03  fof(f10,axiom,(
% 2.88/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f25,plain,(
% 2.88/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.03    inference(ennf_transformation,[],[f10])).
% 2.88/1.03  
% 2.88/1.03  fof(f46,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.03    inference(cnf_transformation,[],[f25])).
% 2.88/1.03  
% 2.88/1.03  fof(f6,axiom,(
% 2.88/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f20,plain,(
% 2.88/1.03    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.88/1.03    inference(ennf_transformation,[],[f6])).
% 2.88/1.03  
% 2.88/1.03  fof(f21,plain,(
% 2.88/1.03    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/1.03    inference(flattening,[],[f20])).
% 2.88/1.03  
% 2.88/1.03  fof(f42,plain,(
% 2.88/1.03    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f21])).
% 2.88/1.03  
% 2.88/1.03  fof(f60,plain,(
% 2.88/1.03    v2_funct_1(sK2)),
% 2.88/1.03    inference(cnf_transformation,[],[f35])).
% 2.88/1.03  
% 2.88/1.03  fof(f57,plain,(
% 2.88/1.03    v1_funct_1(sK2)),
% 2.88/1.03    inference(cnf_transformation,[],[f35])).
% 2.88/1.03  
% 2.88/1.03  fof(f7,axiom,(
% 2.88/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f22,plain,(
% 2.88/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.03    inference(ennf_transformation,[],[f7])).
% 2.88/1.03  
% 2.88/1.03  fof(f43,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.03    inference(cnf_transformation,[],[f22])).
% 2.88/1.03  
% 2.88/1.03  fof(f13,axiom,(
% 2.88/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f29,plain,(
% 2.88/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.88/1.03    inference(ennf_transformation,[],[f13])).
% 2.88/1.03  
% 2.88/1.03  fof(f30,plain,(
% 2.88/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/1.03    inference(flattening,[],[f29])).
% 2.88/1.03  
% 2.88/1.03  fof(f56,plain,(
% 2.88/1.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f30])).
% 2.88/1.03  
% 2.88/1.03  fof(f11,axiom,(
% 2.88/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f26,plain,(
% 2.88/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.03    inference(ennf_transformation,[],[f11])).
% 2.88/1.03  
% 2.88/1.03  fof(f47,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.03    inference(cnf_transformation,[],[f26])).
% 2.88/1.03  
% 2.88/1.03  fof(f61,plain,(
% 2.88/1.03    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.88/1.03    inference(cnf_transformation,[],[f35])).
% 2.88/1.03  
% 2.88/1.03  fof(f41,plain,(
% 2.88/1.03    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f21])).
% 2.88/1.03  
% 2.88/1.03  fof(f5,axiom,(
% 2.88/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f18,plain,(
% 2.88/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.88/1.03    inference(ennf_transformation,[],[f5])).
% 2.88/1.03  
% 2.88/1.03  fof(f19,plain,(
% 2.88/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.88/1.03    inference(flattening,[],[f18])).
% 2.88/1.03  
% 2.88/1.03  fof(f39,plain,(
% 2.88/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f19])).
% 2.88/1.03  
% 2.88/1.03  fof(f40,plain,(
% 2.88/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f19])).
% 2.88/1.03  
% 2.88/1.03  fof(f55,plain,(
% 2.88/1.03    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f30])).
% 2.88/1.03  
% 2.88/1.03  fof(f62,plain,(
% 2.88/1.03    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.88/1.03    inference(cnf_transformation,[],[f35])).
% 2.88/1.03  
% 2.88/1.03  fof(f9,axiom,(
% 2.88/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f24,plain,(
% 2.88/1.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.88/1.03    inference(ennf_transformation,[],[f9])).
% 2.88/1.03  
% 2.88/1.03  fof(f45,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f24])).
% 2.88/1.03  
% 2.88/1.03  fof(f1,axiom,(
% 2.88/1.03    v1_xboole_0(k1_xboole_0)),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f36,plain,(
% 2.88/1.03    v1_xboole_0(k1_xboole_0)),
% 2.88/1.03    inference(cnf_transformation,[],[f1])).
% 2.88/1.03  
% 2.88/1.03  fof(f2,axiom,(
% 2.88/1.03    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f17,plain,(
% 2.88/1.03    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.88/1.03    inference(ennf_transformation,[],[f2])).
% 2.88/1.03  
% 2.88/1.03  fof(f37,plain,(
% 2.88/1.03    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f17])).
% 2.88/1.03  
% 2.88/1.03  fof(f3,axiom,(
% 2.88/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f38,plain,(
% 2.88/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.88/1.03    inference(cnf_transformation,[],[f3])).
% 2.88/1.03  
% 2.88/1.03  fof(f8,axiom,(
% 2.88/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.88/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.03  
% 2.88/1.03  fof(f23,plain,(
% 2.88/1.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.88/1.03    inference(ennf_transformation,[],[f8])).
% 2.88/1.03  
% 2.88/1.03  fof(f44,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.88/1.03    inference(cnf_transformation,[],[f23])).
% 2.88/1.03  
% 2.88/1.03  fof(f51,plain,(
% 2.88/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.03    inference(cnf_transformation,[],[f33])).
% 2.88/1.03  
% 2.88/1.03  fof(f66,plain,(
% 2.88/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.88/1.03    inference(equality_resolution,[],[f51])).
% 2.88/1.03  
% 2.88/1.03  cnf(c_17,plain,
% 2.88/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.88/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.88/1.03      | k1_xboole_0 = X2 ),
% 2.88/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_25,negated_conjecture,
% 2.88/1.03      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.88/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_492,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.88/1.03      | sK0 != X1
% 2.88/1.03      | sK1 != X2
% 2.88/1.03      | sK2 != X0
% 2.88/1.03      | k1_xboole_0 = X2 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_493,plain,
% 2.88/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.88/1.03      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.88/1.03      | k1_xboole_0 = sK1 ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_492]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_24,negated_conjecture,
% 2.88/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.88/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_495,plain,
% 2.88/1.03      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.88/1.03      inference(global_propositional_subsumption,[status(thm)],[c_493,c_24]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_593,plain,
% 2.88/1.03      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_495]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_605,negated_conjecture,
% 2.88/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_24]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1082,plain,
% 2.88/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_10,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_609,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.88/1.03      | k1_relset_1(X1_45,X2_45,X0_45) = k1_relat_1(X0_45) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1079,plain,
% 2.88/1.03      ( k1_relset_1(X0_45,X1_45,X2_45) = k1_relat_1(X2_45)
% 2.88/1.03      | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1834,plain,
% 2.88/1.03      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1082,c_1079]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2043,plain,
% 2.88/1.03      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_593,c_1834]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_5,plain,
% 2.88/1.03      ( ~ v2_funct_1(X0)
% 2.88/1.03      | ~ v1_relat_1(X0)
% 2.88/1.03      | ~ v1_funct_1(X0)
% 2.88/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_23,negated_conjecture,
% 2.88/1.03      ( v2_funct_1(sK2) ),
% 2.88/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_297,plain,
% 2.88/1.03      ( ~ v1_relat_1(X0)
% 2.88/1.03      | ~ v1_funct_1(X0)
% 2.88/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.88/1.03      | sK2 != X0 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_298,plain,
% 2.88/1.03      ( ~ v1_relat_1(sK2)
% 2.88/1.03      | ~ v1_funct_1(sK2)
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_297]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_26,negated_conjecture,
% 2.88/1.03      ( v1_funct_1(sK2) ),
% 2.88/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_300,plain,
% 2.88/1.03      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.88/1.03      inference(global_propositional_subsumption,[status(thm)],[c_298,c_26]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_602,plain,
% 2.88/1.03      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_300]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1085,plain,
% 2.88/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.88/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_7,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_612,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.88/1.03      | v1_relat_1(X0_45) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1307,plain,
% 2.88/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.88/1.03      | v1_relat_1(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_612]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1338,plain,
% 2.88/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_1085,c_24,c_602,c_1307]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_18,plain,
% 2.88/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.88/1.03      | ~ v1_relat_1(X0)
% 2.88/1.03      | ~ v1_funct_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_607,plain,
% 2.88/1.03      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_45),k2_relat_1(X0_45))))
% 2.88/1.03      | ~ v1_relat_1(X0_45)
% 2.88/1.03      | ~ v1_funct_1(X0_45) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_18]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1081,plain,
% 2.88/1.03      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_45),k2_relat_1(X0_45)))) = iProver_top
% 2.88/1.03      | v1_relat_1(X0_45) != iProver_top
% 2.88/1.03      | v1_funct_1(X0_45) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2319,plain,
% 2.88/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.88/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1338,c_1081]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_11,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_608,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.88/1.03      | k2_relset_1(X1_45,X2_45,X0_45) = k2_relat_1(X0_45) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1080,plain,
% 2.88/1.03      ( k2_relset_1(X0_45,X1_45,X2_45) = k2_relat_1(X2_45)
% 2.88/1.03      | m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1844,plain,
% 2.88/1.03      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1082,c_1080]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_22,negated_conjecture,
% 2.88/1.03      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.88/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_606,negated_conjecture,
% 2.88/1.03      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_22]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1849,plain,
% 2.88/1.03      ( k2_relat_1(sK2) = sK1 ),
% 2.88/1.03      inference(light_normalisation,[status(thm)],[c_1844,c_606]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_6,plain,
% 2.88/1.03      ( ~ v2_funct_1(X0)
% 2.88/1.03      | ~ v1_relat_1(X0)
% 2.88/1.03      | ~ v1_funct_1(X0)
% 2.88/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_283,plain,
% 2.88/1.03      ( ~ v1_relat_1(X0)
% 2.88/1.03      | ~ v1_funct_1(X0)
% 2.88/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.88/1.03      | sK2 != X0 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_284,plain,
% 2.88/1.03      ( ~ v1_relat_1(sK2)
% 2.88/1.03      | ~ v1_funct_1(sK2)
% 2.88/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_283]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_286,plain,
% 2.88/1.03      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.88/1.03      inference(global_propositional_subsumption,[status(thm)],[c_284,c_26]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_603,plain,
% 2.88/1.03      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_286]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1084,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.88/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1334,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_1084,c_24,c_603,c_1307]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1935,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_1849,c_1334]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2356,plain,
% 2.88/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.88/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.88/1.03      inference(light_normalisation,[status(thm)],[c_2319,c_1935]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_27,plain,
% 2.88/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_29,plain,
% 2.88/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1308,plain,
% 2.88/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.88/1.03      | v1_relat_1(sK2) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_4,plain,
% 2.88/1.03      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_613,plain,
% 2.88/1.03      ( ~ v1_relat_1(X0_45)
% 2.88/1.03      | v1_relat_1(k2_funct_1(X0_45))
% 2.88/1.03      | ~ v1_funct_1(X0_45) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1433,plain,
% 2.88/1.03      ( v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) | ~ v1_funct_1(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_613]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1434,plain,
% 2.88/1.03      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.88/1.03      | v1_relat_1(sK2) != iProver_top
% 2.88/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1433]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3,plain,
% 2.88/1.03      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.88/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_614,plain,
% 2.88/1.03      ( ~ v1_relat_1(X0_45)
% 2.88/1.03      | ~ v1_funct_1(X0_45)
% 2.88/1.03      | v1_funct_1(k2_funct_1(X0_45)) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1449,plain,
% 2.88/1.03      ( ~ v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_614]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1450,plain,
% 2.88/1.03      ( v1_relat_1(sK2) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.88/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2575,plain,
% 2.88/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_2356,c_27,c_29,c_1308,c_1434,c_1450]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2585,plain,
% 2.88/1.03      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_2575,c_1079]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2587,plain,
% 2.88/1.03      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 2.88/1.03      inference(light_normalisation,[status(thm)],[c_2585,c_1935]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2665,plain,
% 2.88/1.03      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_2043,c_2587]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_19,plain,
% 2.88/1.03      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.88/1.03      | ~ v1_relat_1(X0)
% 2.88/1.03      | ~ v1_funct_1(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_21,negated_conjecture,
% 2.88/1.03      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.88/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.88/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_503,plain,
% 2.88/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ v1_relat_1(X0)
% 2.88/1.03      | ~ v1_funct_1(X0)
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k1_relat_1(X0) != sK1
% 2.88/1.03      | k2_relat_1(X0) != sK0
% 2.88/1.03      | k2_funct_1(sK2) != X0 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_504,plain,
% 2.88/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_503]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_516,plain,
% 2.88/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.88/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_504,c_7]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_592,plain,
% 2.88/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_516]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1094,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_682,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1665,plain,
% 2.88/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.88/1.03      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_1094,c_27,c_29,c_682,c_1308,c_1450]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1666,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.88/1.03      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.88/1.03      inference(renaming,[status(thm)],[c_1665]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1669,plain,
% 2.88/1.03      ( k1_relat_1(sK2) != sK0
% 2.88/1.03      | k2_relat_1(sK2) != sK1
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.88/1.03      inference(light_normalisation,[status(thm)],[c_1666,c_1334,c_1338]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1934,plain,
% 2.88/1.03      ( k1_relat_1(sK2) != sK0
% 2.88/1.03      | sK1 != sK1
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_1849,c_1669]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1938,plain,
% 2.88/1.03      ( k1_relat_1(sK2) != sK0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.88/1.03      inference(equality_resolution_simp,[status(thm)],[c_1934]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2169,plain,
% 2.88/1.03      ( sK1 = k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_2043,c_1938]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2580,plain,
% 2.88/1.03      ( sK1 = k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_2043,c_2575]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2759,plain,
% 2.88/1.03      ( sK1 = k1_xboole_0 ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_2665,c_2169,c_2580]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_9,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.03      | ~ v1_xboole_0(X2)
% 2.88/1.03      | v1_xboole_0(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_610,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.88/1.03      | ~ v1_xboole_0(X2_45)
% 2.88/1.03      | v1_xboole_0(X0_45) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1078,plain,
% 2.88/1.03      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
% 2.88/1.03      | v1_xboole_0(X2_45) != iProver_top
% 2.88/1.03      | v1_xboole_0(X0_45) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2228,plain,
% 2.88/1.03      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1082,c_1078]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2768,plain,
% 2.88/1.03      ( v1_xboole_0(sK2) = iProver_top
% 2.88/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_2759,c_2228]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_0,plain,
% 2.88/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_86,plain,
% 2.88/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_623,plain,
% 2.88/1.03      ( ~ v1_xboole_0(X0_45) | v1_xboole_0(X1_45) | X1_45 != X0_45 ),
% 2.88/1.03      theory(equality) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1428,plain,
% 2.88/1.03      ( ~ v1_xboole_0(X0_45) | v1_xboole_0(sK1) | sK1 != X0_45 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_623]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1429,plain,
% 2.88/1.03      ( sK1 != X0_45
% 2.88/1.03      | v1_xboole_0(X0_45) != iProver_top
% 2.88/1.03      | v1_xboole_0(sK1) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1431,plain,
% 2.88/1.03      ( sK1 != k1_xboole_0
% 2.88/1.03      | v1_xboole_0(sK1) = iProver_top
% 2.88/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1575,plain,
% 2.88/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
% 2.88/1.03      | ~ v1_xboole_0(X1_45)
% 2.88/1.03      | v1_xboole_0(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_610]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2096,plain,
% 2.88/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.88/1.03      | ~ v1_xboole_0(sK1)
% 2.88/1.03      | v1_xboole_0(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1575]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2097,plain,
% 2.88/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.88/1.03      | v1_xboole_0(sK1) != iProver_top
% 2.88/1.03      | v1_xboole_0(sK2) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_2096]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3327,plain,
% 2.88/1.03      ( v1_xboole_0(sK2) = iProver_top ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_2768,c_29,c_86,c_1431,c_2097,c_2169,c_2580]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_617,plain,
% 2.88/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1071,plain,
% 2.88/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1,plain,
% 2.88/1.03      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.88/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_616,plain,
% 2.88/1.03      ( ~ v1_xboole_0(X0_45) | ~ v1_xboole_0(X1_45) | X1_45 = X0_45 ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1072,plain,
% 2.88/1.03      ( X0_45 = X1_45
% 2.88/1.03      | v1_xboole_0(X1_45) != iProver_top
% 2.88/1.03      | v1_xboole_0(X0_45) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1467,plain,
% 2.88/1.03      ( k1_xboole_0 = X0_45 | v1_xboole_0(X0_45) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1071,c_1072]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3332,plain,
% 2.88/1.03      ( sK2 = k1_xboole_0 ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_3327,c_1467]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3541,plain,
% 2.88/1.03      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_3332,c_1338]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3767,plain,
% 2.88/1.03      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)))) = iProver_top
% 2.88/1.03      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_3541,c_1081]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_74,plain,
% 2.88/1.03      ( v1_relat_1(X0) != iProver_top
% 2.88/1.03      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 2.88/1.03      | v1_funct_1(X0) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_76,plain,
% 2.88/1.03      ( v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.88/1.03      | v1_relat_1(k1_xboole_0) != iProver_top
% 2.88/1.03      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_74]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1310,plain,
% 2.88/1.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
% 2.88/1.03      | v1_relat_1(k1_xboole_0) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_612]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1312,plain,
% 2.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
% 2.88/1.03      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2,plain,
% 2.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.88/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_615,plain,
% 2.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1311,plain,
% 2.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_615]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1314,plain,
% 2.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_627,plain,
% 2.88/1.03      ( ~ v1_funct_1(X0_45) | v1_funct_1(X1_45) | X1_45 != X0_45 ),
% 2.88/1.03      theory(equality) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1328,plain,
% 2.88/1.03      ( v1_funct_1(X0_45) | ~ v1_funct_1(sK2) | X0_45 != sK2 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_627]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1329,plain,
% 2.88/1.03      ( X0_45 != sK2
% 2.88/1.03      | v1_funct_1(X0_45) = iProver_top
% 2.88/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1331,plain,
% 2.88/1.03      ( k1_xboole_0 != sK2
% 2.88/1.03      | v1_funct_1(sK2) != iProver_top
% 2.88/1.03      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1329]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1385,plain,
% 2.88/1.03      ( ~ v1_xboole_0(X0_45) | ~ v1_xboole_0(sK2) | X0_45 = sK2 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_616]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1387,plain,
% 2.88/1.03      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1385]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1430,plain,
% 2.88/1.03      ( v1_xboole_0(sK1) | ~ v1_xboole_0(k1_xboole_0) | sK1 != k1_xboole_0 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1428]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1488,plain,
% 2.88/1.03      ( v1_funct_1(X0_45)
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | X0_45 != k2_funct_1(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_627]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1644,plain,
% 2.88/1.03      ( v1_funct_1(k2_funct_1(X0_45))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k2_funct_1(X0_45) != k2_funct_1(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1488]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1646,plain,
% 2.88/1.03      ( k2_funct_1(X0_45) != k2_funct_1(sK2)
% 2.88/1.03      | v1_funct_1(k2_funct_1(X0_45)) = iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1648,plain,
% 2.88/1.03      ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1646]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_626,plain,
% 2.88/1.03      ( X0_45 != X1_45 | k2_funct_1(X0_45) = k2_funct_1(X1_45) ),
% 2.88/1.03      theory(equality) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1645,plain,
% 2.88/1.03      ( X0_45 != sK2 | k2_funct_1(X0_45) = k2_funct_1(sK2) ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_626]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1650,plain,
% 2.88/1.03      ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2) | k1_xboole_0 != sK2 ),
% 2.88/1.03      inference(instantiation,[status(thm)],[c_1645]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3903,plain,
% 2.88/1.03      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)))) = iProver_top ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_3767,c_27,c_24,c_29,c_76,c_0,c_1308,c_1312,c_1314,c_1331,
% 2.88/1.03                 c_1387,c_1430,c_1450,c_1648,c_1650,c_2096,c_2169,c_2580]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3908,plain,
% 2.88/1.03      ( v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top
% 2.88/1.03      | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_3903,c_1078]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2771,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_2759,c_1935]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3532,plain,
% 2.88/1.03      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_3332,c_2771]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_8,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.03      | ~ v1_xboole_0(X1)
% 2.88/1.03      | v1_xboole_0(X0) ),
% 2.88/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_611,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45)))
% 2.88/1.03      | ~ v1_xboole_0(X1_45)
% 2.88/1.03      | v1_xboole_0(X0_45) ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1077,plain,
% 2.88/1.03      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X1_45,X2_45))) != iProver_top
% 2.88/1.03      | v1_xboole_0(X1_45) != iProver_top
% 2.88/1.03      | v1_xboole_0(X0_45) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2321,plain,
% 2.88/1.03      ( v1_relat_1(X0_45) != iProver_top
% 2.88/1.03      | v1_funct_1(X0_45) != iProver_top
% 2.88/1.03      | v1_xboole_0(X0_45) = iProver_top
% 2.88/1.03      | v1_xboole_0(k1_relat_1(X0_45)) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1081,c_1077]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3931,plain,
% 2.88/1.03      ( v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 2.88/1.03      | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.88/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_3532,c_2321]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_4124,plain,
% 2.88/1.03      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_3908,c_27,c_24,c_29,c_76,c_0,c_86,c_1308,c_1312,c_1314,
% 2.88/1.03                 c_1331,c_1387,c_1430,c_1450,c_1648,c_1650,c_2096,c_2169,
% 2.88/1.03                 c_2580,c_3931]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_4129,plain,
% 2.88/1.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_4124,c_1467]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_14,plain,
% 2.88/1.03      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.88/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.88/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_420,plain,
% 2.88/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.88/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.88/1.03      | k2_funct_1(sK2) != X0
% 2.88/1.03      | sK0 != X1
% 2.88/1.03      | sK1 != k1_xboole_0 ),
% 2.88/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_421,plain,
% 2.88/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.88/1.03      | sK1 != k1_xboole_0 ),
% 2.88/1.03      inference(unflattening,[status(thm)],[c_420]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_597,plain,
% 2.88/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.88/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.88/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.88/1.03      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.88/1.03      | sK1 != k1_xboole_0 ),
% 2.88/1.03      inference(subtyping,[status(esa)],[c_421]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1090,plain,
% 2.88/1.03      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.88/1.03      | sK1 != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_676,plain,
% 2.88/1.03      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.88/1.03      | sK1 != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.88/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1560,plain,
% 2.88/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.88/1.03      | sK1 != k1_xboole_0
% 2.88/1.03      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.88/1.03      inference(global_propositional_subsumption,
% 2.88/1.03                [status(thm)],
% 2.88/1.03                [c_1090,c_27,c_29,c_676,c_1308,c_1450]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1561,plain,
% 2.88/1.03      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.88/1.03      | sK1 != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.88/1.03      inference(renaming,[status(thm)],[c_1560]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2775,plain,
% 2.88/1.03      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.88/1.03      | k1_xboole_0 != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_2759,c_1561]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2806,plain,
% 2.88/1.03      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.88/1.03      inference(equality_resolution_simp,[status(thm)],[c_2775]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_4223,plain,
% 2.88/1.03      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.88/1.03      inference(light_normalisation,[status(thm)],[c_2806,c_3332]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_5019,plain,
% 2.88/1.03      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_4129,c_4223]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1073,plain,
% 2.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) = iProver_top ),
% 2.88/1.03      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_1835,plain,
% 2.88/1.03      ( k1_relset_1(X0_45,X1_45,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.88/1.03      inference(superposition,[status(thm)],[c_1073,c_1079]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_5034,plain,
% 2.88/1.03      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.88/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_5019,c_1835]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_5023,plain,
% 2.88/1.03      ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_4129,c_3541]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_2772,plain,
% 2.88/1.03      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_2759,c_1849]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_3535,plain,
% 2.88/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.88/1.03      inference(demodulation,[status(thm)],[c_3332,c_2772]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_5025,plain,
% 2.88/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.88/1.03      inference(light_normalisation,[status(thm)],[c_5023,c_3535]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_5943,plain,
% 2.88/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.88/1.03      inference(global_propositional_subsumption,[status(thm)],[c_5034,c_5025]) ).
% 2.88/1.03  
% 2.88/1.03  cnf(c_5948,plain,
% 2.88/1.03      ( $false ),
% 2.88/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_5943,c_1073]) ).
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/1.03  
% 2.88/1.03  ------                               Statistics
% 2.88/1.03  
% 2.88/1.03  ------ General
% 2.88/1.03  
% 2.88/1.03  abstr_ref_over_cycles:                  0
% 2.88/1.03  abstr_ref_under_cycles:                 0
% 2.88/1.03  gc_basic_clause_elim:                   0
% 2.88/1.03  forced_gc_time:                         0
% 2.88/1.03  parsing_time:                           0.011
% 2.88/1.03  unif_index_cands_time:                  0.
% 2.88/1.03  unif_index_add_time:                    0.
% 2.88/1.03  orderings_time:                         0.
% 2.88/1.03  out_proof_time:                         0.016
% 2.88/1.03  total_time:                             0.207
% 2.88/1.03  num_of_symbols:                         48
% 2.88/1.03  num_of_terms:                           3192
% 2.88/1.03  
% 2.88/1.03  ------ Preprocessing
% 2.88/1.03  
% 2.88/1.03  num_of_splits:                          0
% 2.88/1.03  num_of_split_atoms:                     0
% 2.88/1.03  num_of_reused_defs:                     0
% 2.88/1.03  num_eq_ax_congr_red:                    2
% 2.88/1.03  num_of_sem_filtered_clauses:            1
% 2.88/1.03  num_of_subtypes:                        3
% 2.88/1.03  monotx_restored_types:                  1
% 2.88/1.03  sat_num_of_epr_types:                   0
% 2.88/1.03  sat_num_of_non_cyclic_types:            0
% 2.88/1.03  sat_guarded_non_collapsed_types:        1
% 2.88/1.03  num_pure_diseq_elim:                    0
% 2.88/1.03  simp_replaced_by:                       0
% 2.88/1.03  res_preprocessed:                       111
% 2.88/1.03  prep_upred:                             0
% 2.88/1.03  prep_unflattend:                        43
% 2.88/1.03  smt_new_axioms:                         0
% 2.88/1.03  pred_elim_cands:                        6
% 2.88/1.03  pred_elim:                              2
% 2.88/1.03  pred_elim_cl:                           -1
% 2.88/1.03  pred_elim_cycles:                       3
% 2.88/1.03  merged_defs:                            0
% 2.88/1.03  merged_defs_ncl:                        0
% 2.88/1.03  bin_hyper_res:                          0
% 2.88/1.03  prep_cycles:                            3
% 2.88/1.03  pred_elim_time:                         0.01
% 2.88/1.03  splitting_time:                         0.
% 2.88/1.03  sem_filter_time:                        0.
% 2.88/1.03  monotx_time:                            0.001
% 2.88/1.03  subtype_inf_time:                       0.002
% 2.88/1.03  
% 2.88/1.03  ------ Problem properties
% 2.88/1.03  
% 2.88/1.03  clauses:                                27
% 2.88/1.03  conjectures:                            3
% 2.88/1.03  epr:                                    3
% 2.88/1.03  horn:                                   23
% 2.88/1.03  ground:                                 14
% 2.88/1.03  unary:                                  5
% 2.88/1.03  binary:                                 6
% 2.88/1.03  lits:                                   77
% 2.88/1.03  lits_eq:                                31
% 2.88/1.03  fd_pure:                                0
% 2.88/1.03  fd_pseudo:                              0
% 2.88/1.03  fd_cond:                                1
% 2.88/1.03  fd_pseudo_cond:                         1
% 2.88/1.03  ac_symbols:                             0
% 2.88/1.03  
% 2.88/1.03  ------ Propositional Solver
% 2.88/1.03  
% 2.88/1.03  prop_solver_calls:                      26
% 2.88/1.03  prop_fast_solver_calls:                 1005
% 2.88/1.03  smt_solver_calls:                       0
% 2.88/1.03  smt_fast_solver_calls:                  0
% 2.88/1.03  prop_num_of_clauses:                    2016
% 2.88/1.03  prop_preprocess_simplified:             5980
% 2.88/1.03  prop_fo_subsumed:                       58
% 2.88/1.03  prop_solver_time:                       0.
% 2.88/1.03  smt_solver_time:                        0.
% 2.88/1.03  smt_fast_solver_time:                   0.
% 2.88/1.03  prop_fast_solver_time:                  0.
% 2.88/1.03  prop_unsat_core_time:                   0.
% 2.88/1.03  
% 2.88/1.03  ------ QBF
% 2.88/1.03  
% 2.88/1.03  qbf_q_res:                              0
% 2.88/1.03  qbf_num_tautologies:                    0
% 2.88/1.03  qbf_prep_cycles:                        0
% 2.88/1.03  
% 2.88/1.03  ------ BMC1
% 2.88/1.03  
% 2.88/1.03  bmc1_current_bound:                     -1
% 2.88/1.03  bmc1_last_solved_bound:                 -1
% 2.88/1.03  bmc1_unsat_core_size:                   -1
% 2.88/1.03  bmc1_unsat_core_parents_size:           -1
% 2.88/1.03  bmc1_merge_next_fun:                    0
% 2.88/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.88/1.03  
% 2.88/1.03  ------ Instantiation
% 2.88/1.03  
% 2.88/1.03  inst_num_of_clauses:                    796
% 2.88/1.03  inst_num_in_passive:                    438
% 2.88/1.03  inst_num_in_active:                     344
% 2.88/1.03  inst_num_in_unprocessed:                14
% 2.88/1.03  inst_num_of_loops:                      490
% 2.88/1.03  inst_num_of_learning_restarts:          0
% 2.88/1.03  inst_num_moves_active_passive:          142
% 2.88/1.03  inst_lit_activity:                      0
% 2.88/1.03  inst_lit_activity_moves:                0
% 2.88/1.03  inst_num_tautologies:                   0
% 2.88/1.03  inst_num_prop_implied:                  0
% 2.88/1.03  inst_num_existing_simplified:           0
% 2.88/1.03  inst_num_eq_res_simplified:             0
% 2.88/1.03  inst_num_child_elim:                    0
% 2.88/1.03  inst_num_of_dismatching_blockings:      158
% 2.88/1.03  inst_num_of_non_proper_insts:           690
% 2.88/1.03  inst_num_of_duplicates:                 0
% 2.88/1.03  inst_inst_num_from_inst_to_res:         0
% 2.88/1.03  inst_dismatching_checking_time:         0.
% 2.88/1.03  
% 2.88/1.03  ------ Resolution
% 2.88/1.03  
% 2.88/1.03  res_num_of_clauses:                     0
% 2.88/1.03  res_num_in_passive:                     0
% 2.88/1.03  res_num_in_active:                      0
% 2.88/1.03  res_num_of_loops:                       114
% 2.88/1.03  res_forward_subset_subsumed:            48
% 2.88/1.03  res_backward_subset_subsumed:           4
% 2.88/1.03  res_forward_subsumed:                   0
% 2.88/1.03  res_backward_subsumed:                  0
% 2.88/1.03  res_forward_subsumption_resolution:     4
% 2.88/1.03  res_backward_subsumption_resolution:    0
% 2.88/1.03  res_clause_to_clause_subsumption:       275
% 2.88/1.03  res_orphan_elimination:                 0
% 2.88/1.03  res_tautology_del:                      97
% 2.88/1.03  res_num_eq_res_simplified:              0
% 2.88/1.03  res_num_sel_changes:                    0
% 2.88/1.03  res_moves_from_active_to_pass:          0
% 2.88/1.03  
% 2.88/1.03  ------ Superposition
% 2.88/1.03  
% 2.88/1.03  sup_time_total:                         0.
% 2.88/1.03  sup_time_generating:                    0.
% 2.88/1.03  sup_time_sim_full:                      0.
% 2.88/1.03  sup_time_sim_immed:                     0.
% 2.88/1.03  
% 2.88/1.03  sup_num_of_clauses:                     53
% 2.88/1.03  sup_num_in_active:                      40
% 2.88/1.03  sup_num_in_passive:                     13
% 2.88/1.03  sup_num_of_loops:                       96
% 2.88/1.03  sup_fw_superposition:                   67
% 2.88/1.03  sup_bw_superposition:                   61
% 2.88/1.03  sup_immediate_simplified:               63
% 2.88/1.03  sup_given_eliminated:                   3
% 2.88/1.03  comparisons_done:                       0
% 2.88/1.03  comparisons_avoided:                    5
% 2.88/1.03  
% 2.88/1.03  ------ Simplifications
% 2.88/1.03  
% 2.88/1.03  
% 2.88/1.03  sim_fw_subset_subsumed:                 19
% 2.88/1.03  sim_bw_subset_subsumed:                 3
% 2.88/1.03  sim_fw_subsumed:                        10
% 2.88/1.03  sim_bw_subsumed:                        1
% 2.88/1.03  sim_fw_subsumption_res:                 2
% 2.88/1.03  sim_bw_subsumption_res:                 0
% 2.88/1.03  sim_tautology_del:                      5
% 2.88/1.03  sim_eq_tautology_del:                   24
% 2.88/1.03  sim_eq_res_simp:                        3
% 2.88/1.03  sim_fw_demodulated:                     6
% 2.88/1.03  sim_bw_demodulated:                     57
% 2.88/1.03  sim_light_normalised:                   49
% 2.88/1.03  sim_joinable_taut:                      0
% 2.88/1.03  sim_joinable_simp:                      0
% 2.88/1.03  sim_ac_normalised:                      0
% 2.88/1.03  sim_smt_subsumption:                    0
% 2.88/1.03  
%------------------------------------------------------------------------------
