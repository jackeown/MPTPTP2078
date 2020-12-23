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
% DateTime   : Thu Dec  3 12:02:28 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  177 (2802 expanded)
%              Number of clauses        :  112 (1153 expanded)
%              Number of leaves         :   18 ( 481 expanded)
%              Depth                    :   25
%              Number of atoms          :  534 (13673 expanded)
%              Number of equality atoms :  241 (3361 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f40,plain,
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

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f13,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_759,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1198,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X2_48,X1_48,k3_relset_1(X1_48,X2_48,X0_48)) = k2_relset_1(X1_48,X2_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1196,plain,
    ( k1_relset_1(X0_48,X1_48,k3_relset_1(X1_48,X0_48,X2_48)) = k2_relset_1(X1_48,X0_48,X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_2463,plain,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) = k2_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1198,c_1196])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_760,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k3_relset_1(X1_48,X2_48,X0_48) = k4_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1194,plain,
    ( k3_relset_1(X0_48,X1_48,X2_48) = k4_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_1983,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1198,c_1194])).

cnf(c_2477,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2463,c_760,c_1983])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1188,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_1503,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1188])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_770,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1189,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_1632,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1503,c_1189])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_342,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_26])).

cnf(c_343,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_345,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_29])).

cnf(c_756,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_1201,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_1634,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1632,c_1201])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_412,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_754,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_1203,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_826,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_767,plain,
    ( ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1400,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1401,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_1664,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_xboole_0 = sK0
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1203,c_30,c_826,c_1401,c_1632])).

cnf(c_1665,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1664])).

cnf(c_1748,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
    | sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1634,c_1665])).

cnf(c_2483,plain,
    ( sK0 = k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2477,c_1748])).

cnf(c_2692,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2483])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1193,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_2073,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_1193])).

cnf(c_2694,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_32,c_1748,c_2073,c_2477])).

cnf(c_2076,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2073,c_32])).

cnf(c_2700,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2694,c_2076])).

cnf(c_18,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_442,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_443,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_457,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_443,c_14])).

cnf(c_752,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_1204,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_827,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_1913,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_xboole_0 = sK1
    | sK0 != k1_xboole_0
    | k2_funct_1(sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_30,c_827,c_1401,c_1632])).

cnf(c_1914,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1913])).

cnf(c_1917,plain,
    ( k4_relat_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1914,c_1634])).

cnf(c_2702,plain,
    ( k4_relat_1(sK2) != k1_xboole_0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2694,c_1917])).

cnf(c_2730,plain,
    ( k4_relat_1(sK2) != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2702])).

cnf(c_2742,plain,
    ( k4_relat_1(sK2) != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2700,c_2730])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_311,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_312,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_359,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_312])).

cnf(c_360,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_360,c_24])).

cnf(c_485,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_750,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_485])).

cnf(c_773,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sP0_iProver_split
    | sK1 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_750])).

cnf(c_1206,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_772,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_750])).

cnf(c_1207,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_1332,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1206,c_1207])).

cnf(c_2151,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1332,c_30,c_1401,c_1632])).

cnf(c_2152,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2151])).

cnf(c_2155,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2152,c_1634])).

cnf(c_2159,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2155,c_2076])).

cnf(c_2699,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2694,c_2159])).

cnf(c_5,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_768,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2707,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2694,c_1198])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_4])).

cnf(c_757,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_relat_1(X0_48)
    | k7_relat_1(X0_48,X1_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_1200,plain,
    ( k7_relat_1(X0_48,X1_48) = X0_48
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_3024,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2707,c_1200])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_769,plain,
    ( ~ v1_relat_1(X0_48)
    | k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1190,plain,
    ( k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_1635,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1632,c_1190])).

cnf(c_3039,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3024,c_1635])).

cnf(c_3268,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3039,c_1632])).

cnf(c_3869,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2699,c_768,c_3268])).

cnf(c_761,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1197,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_3872,plain,
    ( sK1 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3869,c_1197])).

cnf(c_3960,plain,
    ( k4_relat_1(sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_32,c_1748,c_1917,c_2073,c_2477,c_3872])).

cnf(c_3962,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3960,c_768,c_3268])).

cnf(c_3963,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3962])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.68/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/0.99  
% 2.68/0.99  ------  iProver source info
% 2.68/0.99  
% 2.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/0.99  git: non_committed_changes: false
% 2.68/0.99  git: last_make_outside_of_git: false
% 2.68/0.99  
% 2.68/0.99  ------ 
% 2.68/0.99  
% 2.68/0.99  ------ Input Options
% 2.68/0.99  
% 2.68/0.99  --out_options                           all
% 2.68/0.99  --tptp_safe_out                         true
% 2.68/0.99  --problem_path                          ""
% 2.68/0.99  --include_path                          ""
% 2.68/0.99  --clausifier                            res/vclausify_rel
% 2.68/0.99  --clausifier_options                    --mode clausify
% 2.68/0.99  --stdin                                 false
% 2.68/0.99  --stats_out                             all
% 2.68/0.99  
% 2.68/0.99  ------ General Options
% 2.68/0.99  
% 2.68/0.99  --fof                                   false
% 2.68/0.99  --time_out_real                         305.
% 2.68/0.99  --time_out_virtual                      -1.
% 2.68/0.99  --symbol_type_check                     false
% 2.68/0.99  --clausify_out                          false
% 2.68/0.99  --sig_cnt_out                           false
% 2.68/0.99  --trig_cnt_out                          false
% 2.68/0.99  --trig_cnt_out_tolerance                1.
% 2.68/0.99  --trig_cnt_out_sk_spl                   false
% 2.68/0.99  --abstr_cl_out                          false
% 2.68/0.99  
% 2.68/0.99  ------ Global Options
% 2.68/0.99  
% 2.68/0.99  --schedule                              default
% 2.68/0.99  --add_important_lit                     false
% 2.68/0.99  --prop_solver_per_cl                    1000
% 2.68/0.99  --min_unsat_core                        false
% 2.68/0.99  --soft_assumptions                      false
% 2.68/0.99  --soft_lemma_size                       3
% 2.68/0.99  --prop_impl_unit_size                   0
% 2.68/0.99  --prop_impl_unit                        []
% 2.68/0.99  --share_sel_clauses                     true
% 2.68/0.99  --reset_solvers                         false
% 2.68/0.99  --bc_imp_inh                            [conj_cone]
% 2.68/0.99  --conj_cone_tolerance                   3.
% 2.68/0.99  --extra_neg_conj                        none
% 2.68/0.99  --large_theory_mode                     true
% 2.68/0.99  --prolific_symb_bound                   200
% 2.68/0.99  --lt_threshold                          2000
% 2.68/0.99  --clause_weak_htbl                      true
% 2.68/0.99  --gc_record_bc_elim                     false
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing Options
% 2.68/0.99  
% 2.68/0.99  --preprocessing_flag                    true
% 2.68/0.99  --time_out_prep_mult                    0.1
% 2.68/0.99  --splitting_mode                        input
% 2.68/0.99  --splitting_grd                         true
% 2.68/0.99  --splitting_cvd                         false
% 2.68/0.99  --splitting_cvd_svl                     false
% 2.68/0.99  --splitting_nvd                         32
% 2.68/0.99  --sub_typing                            true
% 2.68/0.99  --prep_gs_sim                           true
% 2.68/0.99  --prep_unflatten                        true
% 2.68/0.99  --prep_res_sim                          true
% 2.68/0.99  --prep_upred                            true
% 2.68/0.99  --prep_sem_filter                       exhaustive
% 2.68/0.99  --prep_sem_filter_out                   false
% 2.68/0.99  --pred_elim                             true
% 2.68/0.99  --res_sim_input                         true
% 2.68/0.99  --eq_ax_congr_red                       true
% 2.68/0.99  --pure_diseq_elim                       true
% 2.68/0.99  --brand_transform                       false
% 2.68/0.99  --non_eq_to_eq                          false
% 2.68/0.99  --prep_def_merge                        true
% 2.68/0.99  --prep_def_merge_prop_impl              false
% 2.68/0.99  --prep_def_merge_mbd                    true
% 2.68/0.99  --prep_def_merge_tr_red                 false
% 2.68/0.99  --prep_def_merge_tr_cl                  false
% 2.68/0.99  --smt_preprocessing                     true
% 2.68/0.99  --smt_ac_axioms                         fast
% 2.68/0.99  --preprocessed_out                      false
% 2.68/0.99  --preprocessed_stats                    false
% 2.68/0.99  
% 2.68/0.99  ------ Abstraction refinement Options
% 2.68/0.99  
% 2.68/0.99  --abstr_ref                             []
% 2.68/0.99  --abstr_ref_prep                        false
% 2.68/0.99  --abstr_ref_until_sat                   false
% 2.68/0.99  --abstr_ref_sig_restrict                funpre
% 2.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.99  --abstr_ref_under                       []
% 2.68/0.99  
% 2.68/0.99  ------ SAT Options
% 2.68/0.99  
% 2.68/0.99  --sat_mode                              false
% 2.68/0.99  --sat_fm_restart_options                ""
% 2.68/0.99  --sat_gr_def                            false
% 2.68/0.99  --sat_epr_types                         true
% 2.68/0.99  --sat_non_cyclic_types                  false
% 2.68/0.99  --sat_finite_models                     false
% 2.68/0.99  --sat_fm_lemmas                         false
% 2.68/0.99  --sat_fm_prep                           false
% 2.68/0.99  --sat_fm_uc_incr                        true
% 2.68/0.99  --sat_out_model                         small
% 2.68/0.99  --sat_out_clauses                       false
% 2.68/0.99  
% 2.68/0.99  ------ QBF Options
% 2.68/0.99  
% 2.68/0.99  --qbf_mode                              false
% 2.68/0.99  --qbf_elim_univ                         false
% 2.68/0.99  --qbf_dom_inst                          none
% 2.68/0.99  --qbf_dom_pre_inst                      false
% 2.68/0.99  --qbf_sk_in                             false
% 2.68/0.99  --qbf_pred_elim                         true
% 2.68/0.99  --qbf_split                             512
% 2.68/0.99  
% 2.68/0.99  ------ BMC1 Options
% 2.68/0.99  
% 2.68/0.99  --bmc1_incremental                      false
% 2.68/0.99  --bmc1_axioms                           reachable_all
% 2.68/0.99  --bmc1_min_bound                        0
% 2.68/0.99  --bmc1_max_bound                        -1
% 2.68/0.99  --bmc1_max_bound_default                -1
% 2.68/0.99  --bmc1_symbol_reachability              true
% 2.68/0.99  --bmc1_property_lemmas                  false
% 2.68/0.99  --bmc1_k_induction                      false
% 2.68/0.99  --bmc1_non_equiv_states                 false
% 2.68/0.99  --bmc1_deadlock                         false
% 2.68/0.99  --bmc1_ucm                              false
% 2.68/0.99  --bmc1_add_unsat_core                   none
% 2.68/0.99  --bmc1_unsat_core_children              false
% 2.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.99  --bmc1_out_stat                         full
% 2.68/0.99  --bmc1_ground_init                      false
% 2.68/0.99  --bmc1_pre_inst_next_state              false
% 2.68/0.99  --bmc1_pre_inst_state                   false
% 2.68/0.99  --bmc1_pre_inst_reach_state             false
% 2.68/0.99  --bmc1_out_unsat_core                   false
% 2.68/0.99  --bmc1_aig_witness_out                  false
% 2.68/0.99  --bmc1_verbose                          false
% 2.68/0.99  --bmc1_dump_clauses_tptp                false
% 2.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.99  --bmc1_dump_file                        -
% 2.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.99  --bmc1_ucm_extend_mode                  1
% 2.68/0.99  --bmc1_ucm_init_mode                    2
% 2.68/0.99  --bmc1_ucm_cone_mode                    none
% 2.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.99  --bmc1_ucm_relax_model                  4
% 2.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.99  --bmc1_ucm_layered_model                none
% 2.68/0.99  --bmc1_ucm_max_lemma_size               10
% 2.68/0.99  
% 2.68/0.99  ------ AIG Options
% 2.68/0.99  
% 2.68/0.99  --aig_mode                              false
% 2.68/0.99  
% 2.68/0.99  ------ Instantiation Options
% 2.68/0.99  
% 2.68/0.99  --instantiation_flag                    true
% 2.68/0.99  --inst_sos_flag                         false
% 2.68/0.99  --inst_sos_phase                        true
% 2.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel_side                     num_symb
% 2.68/0.99  --inst_solver_per_active                1400
% 2.68/0.99  --inst_solver_calls_frac                1.
% 2.68/0.99  --inst_passive_queue_type               priority_queues
% 2.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.99  --inst_passive_queues_freq              [25;2]
% 2.68/0.99  --inst_dismatching                      true
% 2.68/0.99  --inst_eager_unprocessed_to_passive     true
% 2.68/0.99  --inst_prop_sim_given                   true
% 2.68/0.99  --inst_prop_sim_new                     false
% 2.68/0.99  --inst_subs_new                         false
% 2.68/0.99  --inst_eq_res_simp                      false
% 2.68/0.99  --inst_subs_given                       false
% 2.68/0.99  --inst_orphan_elimination               true
% 2.68/0.99  --inst_learning_loop_flag               true
% 2.68/0.99  --inst_learning_start                   3000
% 2.68/0.99  --inst_learning_factor                  2
% 2.68/0.99  --inst_start_prop_sim_after_learn       3
% 2.68/0.99  --inst_sel_renew                        solver
% 2.68/0.99  --inst_lit_activity_flag                true
% 2.68/0.99  --inst_restr_to_given                   false
% 2.68/0.99  --inst_activity_threshold               500
% 2.68/0.99  --inst_out_proof                        true
% 2.68/0.99  
% 2.68/0.99  ------ Resolution Options
% 2.68/0.99  
% 2.68/0.99  --resolution_flag                       true
% 2.68/0.99  --res_lit_sel                           adaptive
% 2.68/0.99  --res_lit_sel_side                      none
% 2.68/0.99  --res_ordering                          kbo
% 2.68/0.99  --res_to_prop_solver                    active
% 2.68/0.99  --res_prop_simpl_new                    false
% 2.68/0.99  --res_prop_simpl_given                  true
% 2.68/0.99  --res_passive_queue_type                priority_queues
% 2.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.99  --res_passive_queues_freq               [15;5]
% 2.68/0.99  --res_forward_subs                      full
% 2.68/0.99  --res_backward_subs                     full
% 2.68/0.99  --res_forward_subs_resolution           true
% 2.68/0.99  --res_backward_subs_resolution          true
% 2.68/0.99  --res_orphan_elimination                true
% 2.68/0.99  --res_time_limit                        2.
% 2.68/0.99  --res_out_proof                         true
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Options
% 2.68/0.99  
% 2.68/0.99  --superposition_flag                    true
% 2.68/0.99  --sup_passive_queue_type                priority_queues
% 2.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.99  --demod_completeness_check              fast
% 2.68/0.99  --demod_use_ground                      true
% 2.68/0.99  --sup_to_prop_solver                    passive
% 2.68/0.99  --sup_prop_simpl_new                    true
% 2.68/0.99  --sup_prop_simpl_given                  true
% 2.68/0.99  --sup_fun_splitting                     false
% 2.68/0.99  --sup_smt_interval                      50000
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Simplification Setup
% 2.68/0.99  
% 2.68/0.99  --sup_indices_passive                   []
% 2.68/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_full_bw                           [BwDemod]
% 2.68/0.99  --sup_immed_triv                        [TrivRules]
% 2.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_immed_bw_main                     []
% 2.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  
% 2.68/0.99  ------ Combination Options
% 2.68/0.99  
% 2.68/0.99  --comb_res_mult                         3
% 2.68/0.99  --comb_sup_mult                         2
% 2.68/0.99  --comb_inst_mult                        10
% 2.68/0.99  
% 2.68/0.99  ------ Debug Options
% 2.68/0.99  
% 2.68/0.99  --dbg_backtrace                         false
% 2.68/0.99  --dbg_dump_prop_clauses                 false
% 2.68/0.99  --dbg_dump_prop_clauses_file            -
% 2.68/0.99  --dbg_out_stat                          false
% 2.68/0.99  ------ Parsing...
% 2.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.68/0.99  ------ Proving...
% 2.68/0.99  ------ Problem Properties 
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  clauses                                 26
% 2.68/0.99  conjectures                             3
% 2.68/0.99  EPR                                     1
% 2.68/0.99  Horn                                    24
% 2.68/0.99  unary                                   6
% 2.68/0.99  binary                                  8
% 2.68/0.99  lits                                    68
% 2.68/0.99  lits eq                                 26
% 2.68/0.99  fd_pure                                 0
% 2.68/0.99  fd_pseudo                               0
% 2.68/0.99  fd_cond                                 0
% 2.68/0.99  fd_pseudo_cond                          0
% 2.68/0.99  AC symbols                              0
% 2.68/0.99  
% 2.68/0.99  ------ Schedule dynamic 5 is on 
% 2.68/0.99  
% 2.68/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  ------ 
% 2.68/0.99  Current options:
% 2.68/0.99  ------ 
% 2.68/0.99  
% 2.68/0.99  ------ Input Options
% 2.68/0.99  
% 2.68/0.99  --out_options                           all
% 2.68/0.99  --tptp_safe_out                         true
% 2.68/0.99  --problem_path                          ""
% 2.68/0.99  --include_path                          ""
% 2.68/0.99  --clausifier                            res/vclausify_rel
% 2.68/0.99  --clausifier_options                    --mode clausify
% 2.68/0.99  --stdin                                 false
% 2.68/0.99  --stats_out                             all
% 2.68/0.99  
% 2.68/0.99  ------ General Options
% 2.68/0.99  
% 2.68/0.99  --fof                                   false
% 2.68/0.99  --time_out_real                         305.
% 2.68/0.99  --time_out_virtual                      -1.
% 2.68/0.99  --symbol_type_check                     false
% 2.68/0.99  --clausify_out                          false
% 2.68/0.99  --sig_cnt_out                           false
% 2.68/0.99  --trig_cnt_out                          false
% 2.68/0.99  --trig_cnt_out_tolerance                1.
% 2.68/0.99  --trig_cnt_out_sk_spl                   false
% 2.68/0.99  --abstr_cl_out                          false
% 2.68/0.99  
% 2.68/0.99  ------ Global Options
% 2.68/0.99  
% 2.68/0.99  --schedule                              default
% 2.68/0.99  --add_important_lit                     false
% 2.68/0.99  --prop_solver_per_cl                    1000
% 2.68/0.99  --min_unsat_core                        false
% 2.68/0.99  --soft_assumptions                      false
% 2.68/0.99  --soft_lemma_size                       3
% 2.68/0.99  --prop_impl_unit_size                   0
% 2.68/0.99  --prop_impl_unit                        []
% 2.68/0.99  --share_sel_clauses                     true
% 2.68/0.99  --reset_solvers                         false
% 2.68/0.99  --bc_imp_inh                            [conj_cone]
% 2.68/0.99  --conj_cone_tolerance                   3.
% 2.68/0.99  --extra_neg_conj                        none
% 2.68/0.99  --large_theory_mode                     true
% 2.68/0.99  --prolific_symb_bound                   200
% 2.68/0.99  --lt_threshold                          2000
% 2.68/0.99  --clause_weak_htbl                      true
% 2.68/0.99  --gc_record_bc_elim                     false
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing Options
% 2.68/0.99  
% 2.68/0.99  --preprocessing_flag                    true
% 2.68/0.99  --time_out_prep_mult                    0.1
% 2.68/0.99  --splitting_mode                        input
% 2.68/0.99  --splitting_grd                         true
% 2.68/0.99  --splitting_cvd                         false
% 2.68/0.99  --splitting_cvd_svl                     false
% 2.68/0.99  --splitting_nvd                         32
% 2.68/0.99  --sub_typing                            true
% 2.68/0.99  --prep_gs_sim                           true
% 2.68/0.99  --prep_unflatten                        true
% 2.68/0.99  --prep_res_sim                          true
% 2.68/0.99  --prep_upred                            true
% 2.68/0.99  --prep_sem_filter                       exhaustive
% 2.68/0.99  --prep_sem_filter_out                   false
% 2.68/0.99  --pred_elim                             true
% 2.68/0.99  --res_sim_input                         true
% 2.68/0.99  --eq_ax_congr_red                       true
% 2.68/0.99  --pure_diseq_elim                       true
% 2.68/0.99  --brand_transform                       false
% 2.68/0.99  --non_eq_to_eq                          false
% 2.68/0.99  --prep_def_merge                        true
% 2.68/0.99  --prep_def_merge_prop_impl              false
% 2.68/0.99  --prep_def_merge_mbd                    true
% 2.68/0.99  --prep_def_merge_tr_red                 false
% 2.68/0.99  --prep_def_merge_tr_cl                  false
% 2.68/0.99  --smt_preprocessing                     true
% 2.68/0.99  --smt_ac_axioms                         fast
% 2.68/0.99  --preprocessed_out                      false
% 2.68/0.99  --preprocessed_stats                    false
% 2.68/0.99  
% 2.68/0.99  ------ Abstraction refinement Options
% 2.68/0.99  
% 2.68/0.99  --abstr_ref                             []
% 2.68/0.99  --abstr_ref_prep                        false
% 2.68/0.99  --abstr_ref_until_sat                   false
% 2.68/0.99  --abstr_ref_sig_restrict                funpre
% 2.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.99  --abstr_ref_under                       []
% 2.68/0.99  
% 2.68/0.99  ------ SAT Options
% 2.68/0.99  
% 2.68/0.99  --sat_mode                              false
% 2.68/0.99  --sat_fm_restart_options                ""
% 2.68/0.99  --sat_gr_def                            false
% 2.68/0.99  --sat_epr_types                         true
% 2.68/0.99  --sat_non_cyclic_types                  false
% 2.68/0.99  --sat_finite_models                     false
% 2.68/0.99  --sat_fm_lemmas                         false
% 2.68/0.99  --sat_fm_prep                           false
% 2.68/0.99  --sat_fm_uc_incr                        true
% 2.68/0.99  --sat_out_model                         small
% 2.68/0.99  --sat_out_clauses                       false
% 2.68/0.99  
% 2.68/0.99  ------ QBF Options
% 2.68/0.99  
% 2.68/0.99  --qbf_mode                              false
% 2.68/0.99  --qbf_elim_univ                         false
% 2.68/0.99  --qbf_dom_inst                          none
% 2.68/0.99  --qbf_dom_pre_inst                      false
% 2.68/0.99  --qbf_sk_in                             false
% 2.68/0.99  --qbf_pred_elim                         true
% 2.68/0.99  --qbf_split                             512
% 2.68/0.99  
% 2.68/0.99  ------ BMC1 Options
% 2.68/0.99  
% 2.68/0.99  --bmc1_incremental                      false
% 2.68/0.99  --bmc1_axioms                           reachable_all
% 2.68/0.99  --bmc1_min_bound                        0
% 2.68/0.99  --bmc1_max_bound                        -1
% 2.68/0.99  --bmc1_max_bound_default                -1
% 2.68/0.99  --bmc1_symbol_reachability              true
% 2.68/0.99  --bmc1_property_lemmas                  false
% 2.68/0.99  --bmc1_k_induction                      false
% 2.68/0.99  --bmc1_non_equiv_states                 false
% 2.68/0.99  --bmc1_deadlock                         false
% 2.68/0.99  --bmc1_ucm                              false
% 2.68/0.99  --bmc1_add_unsat_core                   none
% 2.68/0.99  --bmc1_unsat_core_children              false
% 2.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.99  --bmc1_out_stat                         full
% 2.68/0.99  --bmc1_ground_init                      false
% 2.68/0.99  --bmc1_pre_inst_next_state              false
% 2.68/0.99  --bmc1_pre_inst_state                   false
% 2.68/0.99  --bmc1_pre_inst_reach_state             false
% 2.68/0.99  --bmc1_out_unsat_core                   false
% 2.68/0.99  --bmc1_aig_witness_out                  false
% 2.68/0.99  --bmc1_verbose                          false
% 2.68/0.99  --bmc1_dump_clauses_tptp                false
% 2.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.99  --bmc1_dump_file                        -
% 2.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.99  --bmc1_ucm_extend_mode                  1
% 2.68/0.99  --bmc1_ucm_init_mode                    2
% 2.68/0.99  --bmc1_ucm_cone_mode                    none
% 2.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.99  --bmc1_ucm_relax_model                  4
% 2.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.99  --bmc1_ucm_layered_model                none
% 2.68/0.99  --bmc1_ucm_max_lemma_size               10
% 2.68/0.99  
% 2.68/0.99  ------ AIG Options
% 2.68/0.99  
% 2.68/0.99  --aig_mode                              false
% 2.68/0.99  
% 2.68/0.99  ------ Instantiation Options
% 2.68/0.99  
% 2.68/0.99  --instantiation_flag                    true
% 2.68/0.99  --inst_sos_flag                         false
% 2.68/0.99  --inst_sos_phase                        true
% 2.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.99  --inst_lit_sel_side                     none
% 2.68/0.99  --inst_solver_per_active                1400
% 2.68/0.99  --inst_solver_calls_frac                1.
% 2.68/0.99  --inst_passive_queue_type               priority_queues
% 2.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.99  --inst_passive_queues_freq              [25;2]
% 2.68/0.99  --inst_dismatching                      true
% 2.68/0.99  --inst_eager_unprocessed_to_passive     true
% 2.68/0.99  --inst_prop_sim_given                   true
% 2.68/0.99  --inst_prop_sim_new                     false
% 2.68/0.99  --inst_subs_new                         false
% 2.68/0.99  --inst_eq_res_simp                      false
% 2.68/0.99  --inst_subs_given                       false
% 2.68/0.99  --inst_orphan_elimination               true
% 2.68/0.99  --inst_learning_loop_flag               true
% 2.68/0.99  --inst_learning_start                   3000
% 2.68/0.99  --inst_learning_factor                  2
% 2.68/0.99  --inst_start_prop_sim_after_learn       3
% 2.68/0.99  --inst_sel_renew                        solver
% 2.68/0.99  --inst_lit_activity_flag                true
% 2.68/0.99  --inst_restr_to_given                   false
% 2.68/0.99  --inst_activity_threshold               500
% 2.68/0.99  --inst_out_proof                        true
% 2.68/0.99  
% 2.68/0.99  ------ Resolution Options
% 2.68/0.99  
% 2.68/0.99  --resolution_flag                       false
% 2.68/0.99  --res_lit_sel                           adaptive
% 2.68/0.99  --res_lit_sel_side                      none
% 2.68/0.99  --res_ordering                          kbo
% 2.68/0.99  --res_to_prop_solver                    active
% 2.68/0.99  --res_prop_simpl_new                    false
% 2.68/0.99  --res_prop_simpl_given                  true
% 2.68/0.99  --res_passive_queue_type                priority_queues
% 2.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.99  --res_passive_queues_freq               [15;5]
% 2.68/0.99  --res_forward_subs                      full
% 2.68/0.99  --res_backward_subs                     full
% 2.68/0.99  --res_forward_subs_resolution           true
% 2.68/0.99  --res_backward_subs_resolution          true
% 2.68/0.99  --res_orphan_elimination                true
% 2.68/0.99  --res_time_limit                        2.
% 2.68/0.99  --res_out_proof                         true
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Options
% 2.68/0.99  
% 2.68/0.99  --superposition_flag                    true
% 2.68/0.99  --sup_passive_queue_type                priority_queues
% 2.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.99  --demod_completeness_check              fast
% 2.68/0.99  --demod_use_ground                      true
% 2.68/0.99  --sup_to_prop_solver                    passive
% 2.68/0.99  --sup_prop_simpl_new                    true
% 2.68/0.99  --sup_prop_simpl_given                  true
% 2.68/0.99  --sup_fun_splitting                     false
% 2.68/0.99  --sup_smt_interval                      50000
% 2.68/0.99  
% 2.68/0.99  ------ Superposition Simplification Setup
% 2.68/0.99  
% 2.68/0.99  --sup_indices_passive                   []
% 2.68/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_full_bw                           [BwDemod]
% 2.68/0.99  --sup_immed_triv                        [TrivRules]
% 2.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_immed_bw_main                     []
% 2.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.99  
% 2.68/0.99  ------ Combination Options
% 2.68/0.99  
% 2.68/0.99  --comb_res_mult                         3
% 2.68/0.99  --comb_sup_mult                         2
% 2.68/0.99  --comb_inst_mult                        10
% 2.68/0.99  
% 2.68/0.99  ------ Debug Options
% 2.68/0.99  
% 2.68/0.99  --dbg_backtrace                         false
% 2.68/0.99  --dbg_dump_prop_clauses                 false
% 2.68/0.99  --dbg_dump_prop_clauses_file            -
% 2.68/0.99  --dbg_out_stat                          false
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  ------ Proving...
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  % SZS status Theorem for theBenchmark.p
% 2.68/0.99  
% 2.68/0.99   Resolution empty clause
% 2.68/0.99  
% 2.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  fof(f17,conjecture,(
% 2.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f18,negated_conjecture,(
% 2.68/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.68/0.99    inference(negated_conjecture,[],[f17])).
% 2.68/0.99  
% 2.68/0.99  fof(f37,plain,(
% 2.68/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.68/0.99    inference(ennf_transformation,[],[f18])).
% 2.68/0.99  
% 2.68/0.99  fof(f38,plain,(
% 2.68/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.68/0.99    inference(flattening,[],[f37])).
% 2.68/0.99  
% 2.68/0.99  fof(f40,plain,(
% 2.68/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.68/0.99    introduced(choice_axiom,[])).
% 2.68/0.99  
% 2.68/0.99  fof(f41,plain,(
% 2.68/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40])).
% 2.68/0.99  
% 2.68/0.99  fof(f68,plain,(
% 2.68/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.68/0.99    inference(cnf_transformation,[],[f41])).
% 2.68/0.99  
% 2.68/0.99  fof(f12,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f31,plain,(
% 2.68/0.99    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f12])).
% 2.68/0.99  
% 2.68/0.99  fof(f54,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f31])).
% 2.68/0.99  
% 2.68/0.99  fof(f70,plain,(
% 2.68/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.68/0.99    inference(cnf_transformation,[],[f41])).
% 2.68/0.99  
% 2.68/0.99  fof(f11,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f30,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f11])).
% 2.68/0.99  
% 2.68/0.99  fof(f53,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f30])).
% 2.68/0.99  
% 2.68/0.99  fof(f2,axiom,(
% 2.68/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f20,plain,(
% 2.68/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.68/0.99    inference(ennf_transformation,[],[f2])).
% 2.68/0.99  
% 2.68/0.99  fof(f43,plain,(
% 2.68/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f20])).
% 2.68/0.99  
% 2.68/0.99  fof(f3,axiom,(
% 2.68/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f44,plain,(
% 2.68/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f3])).
% 2.68/0.99  
% 2.68/0.99  fof(f7,axiom,(
% 2.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f24,plain,(
% 2.68/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.68/0.99    inference(ennf_transformation,[],[f7])).
% 2.68/0.99  
% 2.68/0.99  fof(f25,plain,(
% 2.68/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.68/0.99    inference(flattening,[],[f24])).
% 2.68/0.99  
% 2.68/0.99  fof(f48,plain,(
% 2.68/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f25])).
% 2.68/0.99  
% 2.68/0.99  fof(f69,plain,(
% 2.68/0.99    v2_funct_1(sK2)),
% 2.68/0.99    inference(cnf_transformation,[],[f41])).
% 2.68/0.99  
% 2.68/0.99  fof(f66,plain,(
% 2.68/0.99    v1_funct_1(sK2)),
% 2.68/0.99    inference(cnf_transformation,[],[f41])).
% 2.68/0.99  
% 2.68/0.99  fof(f16,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f35,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f16])).
% 2.68/0.99  
% 2.68/0.99  fof(f36,plain,(
% 2.68/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(flattening,[],[f35])).
% 2.68/0.99  
% 2.68/0.99  fof(f39,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(nnf_transformation,[],[f36])).
% 2.68/0.99  
% 2.68/0.99  fof(f62,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f39])).
% 2.68/0.99  
% 2.68/0.99  fof(f71,plain,(
% 2.68/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.68/0.99    inference(cnf_transformation,[],[f41])).
% 2.68/0.99  
% 2.68/0.99  fof(f8,axiom,(
% 2.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f26,plain,(
% 2.68/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.68/0.99    inference(ennf_transformation,[],[f8])).
% 2.68/0.99  
% 2.68/0.99  fof(f27,plain,(
% 2.68/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.68/0.99    inference(flattening,[],[f26])).
% 2.68/0.99  
% 2.68/0.99  fof(f50,plain,(
% 2.68/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f27])).
% 2.68/0.99  
% 2.68/0.99  fof(f10,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f29,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f10])).
% 2.68/0.99  
% 2.68/0.99  fof(f52,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f29])).
% 2.68/0.99  
% 2.68/0.99  fof(f65,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f39])).
% 2.68/0.99  
% 2.68/0.99  fof(f72,plain,(
% 2.68/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(equality_resolution,[],[f65])).
% 2.68/0.99  
% 2.68/0.99  fof(f73,plain,(
% 2.68/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.68/0.99    inference(equality_resolution,[],[f72])).
% 2.68/0.99  
% 2.68/0.99  fof(f13,axiom,(
% 2.68/0.99    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f56,plain,(
% 2.68/0.99    ( ! [X0,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f13])).
% 2.68/0.99  
% 2.68/0.99  fof(f14,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f32,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f14])).
% 2.68/0.99  
% 2.68/0.99  fof(f33,plain,(
% 2.68/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(flattening,[],[f32])).
% 2.68/0.99  
% 2.68/0.99  fof(f58,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f33])).
% 2.68/0.99  
% 2.68/0.99  fof(f1,axiom,(
% 2.68/0.99    v1_xboole_0(k1_xboole_0)),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f42,plain,(
% 2.68/0.99    v1_xboole_0(k1_xboole_0)),
% 2.68/0.99    inference(cnf_transformation,[],[f1])).
% 2.68/0.99  
% 2.68/0.99  fof(f15,axiom,(
% 2.68/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f34,plain,(
% 2.68/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.68/0.99    inference(ennf_transformation,[],[f15])).
% 2.68/0.99  
% 2.68/0.99  fof(f59,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f34])).
% 2.68/0.99  
% 2.68/0.99  fof(f6,axiom,(
% 2.68/0.99    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f47,plain,(
% 2.68/0.99    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 2.68/0.99    inference(cnf_transformation,[],[f6])).
% 2.68/0.99  
% 2.68/0.99  fof(f9,axiom,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f19,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.68/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.68/0.99  
% 2.68/0.99  fof(f28,plain,(
% 2.68/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.68/0.99    inference(ennf_transformation,[],[f19])).
% 2.68/0.99  
% 2.68/0.99  fof(f51,plain,(
% 2.68/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.68/0.99    inference(cnf_transformation,[],[f28])).
% 2.68/0.99  
% 2.68/0.99  fof(f5,axiom,(
% 2.68/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f22,plain,(
% 2.68/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.68/0.99    inference(ennf_transformation,[],[f5])).
% 2.68/0.99  
% 2.68/0.99  fof(f23,plain,(
% 2.68/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.68/0.99    inference(flattening,[],[f22])).
% 2.68/0.99  
% 2.68/0.99  fof(f46,plain,(
% 2.68/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f23])).
% 2.68/0.99  
% 2.68/0.99  fof(f4,axiom,(
% 2.68/0.99    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 2.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.99  
% 2.68/0.99  fof(f21,plain,(
% 2.68/0.99    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 2.68/0.99    inference(ennf_transformation,[],[f4])).
% 2.68/0.99  
% 2.68/0.99  fof(f45,plain,(
% 2.68/0.99    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.68/0.99    inference(cnf_transformation,[],[f21])).
% 2.68/0.99  
% 2.68/0.99  cnf(c_27,negated_conjecture,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_759,negated_conjecture,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1198,plain,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_13,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_762,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.68/0.99      | k1_relset_1(X2_48,X1_48,k3_relset_1(X1_48,X2_48,X0_48)) = k2_relset_1(X1_48,X2_48,X0_48) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1196,plain,
% 2.68/0.99      ( k1_relset_1(X0_48,X1_48,k3_relset_1(X1_48,X0_48,X2_48)) = k2_relset_1(X1_48,X0_48,X2_48)
% 2.68/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2463,plain,
% 2.68/0.99      ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) = k2_relset_1(sK0,sK1,sK2) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1198,c_1196]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_25,negated_conjecture,
% 2.68/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.68/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_760,negated_conjecture,
% 2.68/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_11,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_764,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.68/0.99      | k3_relset_1(X1_48,X2_48,X0_48) = k4_relat_1(X0_48) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1194,plain,
% 2.68/0.99      ( k3_relset_1(X0_48,X1_48,X2_48) = k4_relat_1(X2_48)
% 2.68/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1983,plain,
% 2.68/0.99      ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1198,c_1194]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2477,plain,
% 2.68/0.99      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_2463,c_760,c_1983]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_771,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.68/0.99      | ~ v1_relat_1(X1_48)
% 2.68/0.99      | v1_relat_1(X0_48) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1188,plain,
% 2.68/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 2.68/0.99      | v1_relat_1(X1_48) != iProver_top
% 2.68/0.99      | v1_relat_1(X0_48) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1503,plain,
% 2.68/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.68/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1198,c_1188]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2,plain,
% 2.68/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.68/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_770,plain,
% 2.68/0.99      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1189,plain,
% 2.68/0.99      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1632,plain,
% 2.68/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.68/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1503,c_1189]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_6,plain,
% 2.68/0.99      ( ~ v1_funct_1(X0)
% 2.68/0.99      | ~ v2_funct_1(X0)
% 2.68/0.99      | ~ v1_relat_1(X0)
% 2.68/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_26,negated_conjecture,
% 2.68/0.99      ( v2_funct_1(sK2) ),
% 2.68/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_342,plain,
% 2.68/0.99      ( ~ v1_funct_1(X0)
% 2.68/0.99      | ~ v1_relat_1(X0)
% 2.68/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.68/0.99      | sK2 != X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_26]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_343,plain,
% 2.68/0.99      ( ~ v1_funct_1(sK2)
% 2.68/0.99      | ~ v1_relat_1(sK2)
% 2.68/0.99      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_342]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_29,negated_conjecture,
% 2.68/0.99      ( v1_funct_1(sK2) ),
% 2.68/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_345,plain,
% 2.68/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_343,c_29]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_756,plain,
% 2.68/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_345]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1201,plain,
% 2.68/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) | v1_relat_1(sK2) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1634,plain,
% 2.68/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1632,c_1201]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_21,plain,
% 2.68/0.99      ( v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.68/0.99      | k1_xboole_0 = X2 ),
% 2.68/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_24,negated_conjecture,
% 2.68/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.68/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_411,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.68/0.99      | k2_funct_1(sK2) != X0
% 2.68/0.99      | sK0 != X2
% 2.68/0.99      | sK1 != X1
% 2.68/0.99      | k1_xboole_0 = X2 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_412,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.68/0.99      | k1_xboole_0 = sK0 ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_411]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_754,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.68/0.99      | k1_xboole_0 = sK0 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_412]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1203,plain,
% 2.68/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.68/0.99      | k1_xboole_0 = sK0
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_30,plain,
% 2.68/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_826,plain,
% 2.68/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.68/0.99      | k1_xboole_0 = sK0
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_7,plain,
% 2.68/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_767,plain,
% 2.68/0.99      ( ~ v1_funct_1(X0_48)
% 2.68/0.99      | v1_funct_1(k2_funct_1(X0_48))
% 2.68/0.99      | ~ v1_relat_1(X0_48) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1400,plain,
% 2.68/0.99      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.68/0.99      inference(instantiation,[status(thm)],[c_767]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1401,plain,
% 2.68/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.68/0.99      | v1_funct_1(sK2) != iProver_top
% 2.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1664,plain,
% 2.68/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | k1_xboole_0 = sK0
% 2.68/0.99      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_1203,c_30,c_826,c_1401,c_1632]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1665,plain,
% 2.68/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.68/0.99      | k1_xboole_0 = sK0
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.68/0.99      inference(renaming,[status(thm)],[c_1664]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1748,plain,
% 2.68/0.99      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
% 2.68/0.99      | sK0 = k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_1634,c_1665]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2483,plain,
% 2.68/0.99      ( sK0 = k1_xboole_0
% 2.68/0.99      | sK1 != sK1
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2477,c_1748]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2692,plain,
% 2.68/0.99      ( sK0 = k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.68/0.99      inference(equality_resolution_simp,[status(thm)],[c_2483]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_32,plain,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_10,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_765,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.68/0.99      | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1193,plain,
% 2.68/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.68/0.99      | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2073,plain,
% 2.68/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 2.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1983,c_1193]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2694,plain,
% 2.68/0.99      ( sK0 = k1_xboole_0 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_2692,c_32,c_1748,c_2073,c_2477]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2076,plain,
% 2.68/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2073,c_32]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2700,plain,
% 2.68/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2694,c_2076]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_18,plain,
% 2.68/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.68/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.68/0.99      | k1_xboole_0 = X0 ),
% 2.68/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_442,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k2_funct_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | sK1 != X0
% 2.68/0.99      | k1_xboole_0 = X0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_443,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k2_funct_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | k1_xboole_0 = sK1 ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_442]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_14,plain,
% 2.68/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_457,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k2_funct_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | k1_xboole_0 = sK1 ),
% 2.68/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_443,c_14]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_752,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k2_funct_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | k1_xboole_0 = sK1 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_457]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1204,plain,
% 2.68/0.99      ( k2_funct_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | k1_xboole_0 = sK1
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_827,plain,
% 2.68/0.99      ( k2_funct_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | k1_xboole_0 = sK1
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1913,plain,
% 2.68/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | k1_xboole_0 = sK1
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | k2_funct_1(sK2) != k1_xboole_0 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_1204,c_30,c_827,c_1401,c_1632]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1914,plain,
% 2.68/0.99      ( k2_funct_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | k1_xboole_0 = sK1
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.68/0.99      inference(renaming,[status(thm)],[c_1913]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1917,plain,
% 2.68/0.99      ( k4_relat_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK0 != k1_xboole_0
% 2.68/0.99      | sK1 = k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_1914,c_1634]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2702,plain,
% 2.68/0.99      ( k4_relat_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK1 = k1_xboole_0
% 2.68/0.99      | k1_xboole_0 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2694,c_1917]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2730,plain,
% 2.68/0.99      ( k4_relat_1(sK2) != k1_xboole_0
% 2.68/0.99      | sK1 = k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.68/0.99      inference(equality_resolution_simp,[status(thm)],[c_2702]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2742,plain,
% 2.68/0.99      ( k4_relat_1(sK2) != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2700,c_2730]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_15,plain,
% 2.68/0.99      ( v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ v1_partfun1(X0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_funct_1(X0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_0,plain,
% 2.68/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.68/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_17,plain,
% 2.68/0.99      ( v1_partfun1(X0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_xboole_0(X1) ),
% 2.68/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_311,plain,
% 2.68/0.99      ( v1_partfun1(X0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | k1_xboole_0 != X1 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_312,plain,
% 2.68/0.99      ( v1_partfun1(X0,k1_xboole_0)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_311]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_359,plain,
% 2.68/0.99      ( v1_funct_2(X0,X1,X2)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | X3 != X0
% 2.68/0.99      | k1_xboole_0 != X1 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_312]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_360,plain,
% 2.68/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.68/0.99      | ~ v1_funct_1(X0) ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_484,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ v1_funct_1(X0)
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | k2_funct_1(sK2) != X0
% 2.68/0.99      | sK0 != X1
% 2.68/0.99      | sK1 != k1_xboole_0 ),
% 2.68/0.99      inference(resolution_lifted,[status(thm)],[c_360,c_24]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_485,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | sK1 != k1_xboole_0 ),
% 2.68/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_750,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | sK1 != k1_xboole_0 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_485]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_773,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.68/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.68/0.99      | sP0_iProver_split
% 2.68/0.99      | sK1 != k1_xboole_0 ),
% 2.68/0.99      inference(splitting,
% 2.68/0.99                [splitting(split),new_symbols(definition,[])],
% 2.68/0.99                [c_750]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1206,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.68/0.99      | sP0_iProver_split = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_772,plain,
% 2.68/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
% 2.68/0.99      | ~ sP0_iProver_split ),
% 2.68/0.99      inference(splitting,
% 2.68/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.68/0.99                [c_750]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1207,plain,
% 2.68/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48))) != iProver_top
% 2.68/0.99      | sP0_iProver_split != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1332,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.68/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1206,c_1207]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2151,plain,
% 2.68/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | sK1 != k1_xboole_0 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_1332,c_30,c_1401,c_1632]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2152,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.68/0.99      inference(renaming,[status(thm)],[c_2151]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2155,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_2152,c_1634]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2159,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.68/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2155,c_2076]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2699,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2694,c_2159]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_5,plain,
% 2.68/0.99      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.68/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_768,plain,
% 2.68/0.99      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_2707,plain,
% 2.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.68/0.99      inference(demodulation,[status(thm)],[c_2694,c_1198]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_9,plain,
% 2.68/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.68/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_4,plain,
% 2.68/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.68/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_326,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.68/0.99      | ~ v1_relat_1(X0)
% 2.68/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.68/0.99      inference(resolution,[status(thm)],[c_9,c_4]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_757,plain,
% 2.68/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.68/0.99      | ~ v1_relat_1(X0_48)
% 2.68/0.99      | k7_relat_1(X0_48,X1_48) = X0_48 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_326]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1200,plain,
% 2.68/0.99      ( k7_relat_1(X0_48,X1_48) = X0_48
% 2.68/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.68/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3024,plain,
% 2.68/0.99      ( k7_relat_1(sK2,k1_xboole_0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_2707,c_1200]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.68/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_769,plain,
% 2.68/0.99      ( ~ v1_relat_1(X0_48) | k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0 ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1190,plain,
% 2.68/0.99      ( k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0
% 2.68/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1635,plain,
% 2.68/0.99      ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 2.68/0.99      inference(superposition,[status(thm)],[c_1632,c_1190]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3039,plain,
% 2.68/0.99      ( sK2 = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_3024,c_1635]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3268,plain,
% 2.68/0.99      ( sK2 = k1_xboole_0 ),
% 2.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3039,c_1632]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3869,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0
% 2.68/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_2699,c_768,c_3268]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_761,plain,
% 2.68/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) ),
% 2.68/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_1197,plain,
% 2.68/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) = iProver_top ),
% 2.68/0.99      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3872,plain,
% 2.68/0.99      ( sK1 != k1_xboole_0 ),
% 2.68/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3869,c_1197]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3960,plain,
% 2.68/0.99      ( k4_relat_1(sK2) != k1_xboole_0 ),
% 2.68/0.99      inference(global_propositional_subsumption,
% 2.68/0.99                [status(thm)],
% 2.68/0.99                [c_2742,c_32,c_1748,c_1917,c_2073,c_2477,c_3872]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3962,plain,
% 2.68/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 2.68/0.99      inference(light_normalisation,[status(thm)],[c_3960,c_768,c_3268]) ).
% 2.68/0.99  
% 2.68/0.99  cnf(c_3963,plain,
% 2.68/0.99      ( $false ),
% 2.68/0.99      inference(equality_resolution_simp,[status(thm)],[c_3962]) ).
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/0.99  
% 2.68/0.99  ------                               Statistics
% 2.68/0.99  
% 2.68/0.99  ------ General
% 2.68/0.99  
% 2.68/0.99  abstr_ref_over_cycles:                  0
% 2.68/0.99  abstr_ref_under_cycles:                 0
% 2.68/0.99  gc_basic_clause_elim:                   0
% 2.68/0.99  forced_gc_time:                         0
% 2.68/0.99  parsing_time:                           0.012
% 2.68/0.99  unif_index_cands_time:                  0.
% 2.68/0.99  unif_index_add_time:                    0.
% 2.68/0.99  orderings_time:                         0.
% 2.68/0.99  out_proof_time:                         0.026
% 2.68/0.99  total_time:                             0.175
% 2.68/0.99  num_of_symbols:                         54
% 2.68/0.99  num_of_terms:                           3199
% 2.68/0.99  
% 2.68/0.99  ------ Preprocessing
% 2.68/0.99  
% 2.68/0.99  num_of_splits:                          1
% 2.68/0.99  num_of_split_atoms:                     1
% 2.68/0.99  num_of_reused_defs:                     0
% 2.68/0.99  num_eq_ax_congr_red:                    17
% 2.68/0.99  num_of_sem_filtered_clauses:            1
% 2.68/0.99  num_of_subtypes:                        2
% 2.68/0.99  monotx_restored_types:                  0
% 2.68/0.99  sat_num_of_epr_types:                   0
% 2.68/0.99  sat_num_of_non_cyclic_types:            0
% 2.68/0.99  sat_guarded_non_collapsed_types:        1
% 2.68/0.99  num_pure_diseq_elim:                    0
% 2.68/0.99  simp_replaced_by:                       0
% 2.68/0.99  res_preprocessed:                       133
% 2.68/0.99  prep_upred:                             0
% 2.68/0.99  prep_unflattend:                        45
% 2.68/0.99  smt_new_axioms:                         0
% 2.68/0.99  pred_elim_cands:                        3
% 2.68/0.99  pred_elim:                              5
% 2.68/0.99  pred_elim_cl:                           4
% 2.68/0.99  pred_elim_cycles:                       7
% 2.68/0.99  merged_defs:                            0
% 2.68/0.99  merged_defs_ncl:                        0
% 2.68/0.99  bin_hyper_res:                          0
% 2.68/0.99  prep_cycles:                            4
% 2.68/0.99  pred_elim_time:                         0.011
% 2.68/0.99  splitting_time:                         0.
% 2.68/0.99  sem_filter_time:                        0.
% 2.68/0.99  monotx_time:                            0.
% 2.68/0.99  subtype_inf_time:                       0.
% 2.68/0.99  
% 2.68/0.99  ------ Problem properties
% 2.68/0.99  
% 2.68/0.99  clauses:                                26
% 2.68/0.99  conjectures:                            3
% 2.68/0.99  epr:                                    1
% 2.68/0.99  horn:                                   24
% 2.68/0.99  ground:                                 13
% 2.68/0.99  unary:                                  6
% 2.68/0.99  binary:                                 8
% 2.68/0.99  lits:                                   68
% 2.68/0.99  lits_eq:                                26
% 2.68/0.99  fd_pure:                                0
% 2.68/0.99  fd_pseudo:                              0
% 2.68/0.99  fd_cond:                                0
% 2.68/0.99  fd_pseudo_cond:                         0
% 2.68/0.99  ac_symbols:                             0
% 2.68/0.99  
% 2.68/0.99  ------ Propositional Solver
% 2.68/0.99  
% 2.68/0.99  prop_solver_calls:                      29
% 2.68/0.99  prop_fast_solver_calls:                 888
% 2.68/0.99  smt_solver_calls:                       0
% 2.68/0.99  smt_fast_solver_calls:                  0
% 2.68/0.99  prop_num_of_clauses:                    1353
% 2.68/0.99  prop_preprocess_simplified:             4752
% 2.68/0.99  prop_fo_subsumed:                       17
% 2.68/0.99  prop_solver_time:                       0.
% 2.68/0.99  smt_solver_time:                        0.
% 2.68/0.99  smt_fast_solver_time:                   0.
% 2.68/0.99  prop_fast_solver_time:                  0.
% 2.68/0.99  prop_unsat_core_time:                   0.
% 2.68/0.99  
% 2.68/0.99  ------ QBF
% 2.68/0.99  
% 2.68/0.99  qbf_q_res:                              0
% 2.68/0.99  qbf_num_tautologies:                    0
% 2.68/0.99  qbf_prep_cycles:                        0
% 2.68/0.99  
% 2.68/0.99  ------ BMC1
% 2.68/0.99  
% 2.68/0.99  bmc1_current_bound:                     -1
% 2.68/0.99  bmc1_last_solved_bound:                 -1
% 2.68/0.99  bmc1_unsat_core_size:                   -1
% 2.68/0.99  bmc1_unsat_core_parents_size:           -1
% 2.68/0.99  bmc1_merge_next_fun:                    0
% 2.68/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.68/0.99  
% 2.68/0.99  ------ Instantiation
% 2.68/0.99  
% 2.68/0.99  inst_num_of_clauses:                    471
% 2.68/0.99  inst_num_in_passive:                    84
% 2.68/0.99  inst_num_in_active:                     245
% 2.68/0.99  inst_num_in_unprocessed:                143
% 2.68/0.99  inst_num_of_loops:                      330
% 2.68/0.99  inst_num_of_learning_restarts:          0
% 2.68/0.99  inst_num_moves_active_passive:          80
% 2.68/0.99  inst_lit_activity:                      0
% 2.68/0.99  inst_lit_activity_moves:                0
% 2.68/0.99  inst_num_tautologies:                   0
% 2.68/0.99  inst_num_prop_implied:                  0
% 2.68/0.99  inst_num_existing_simplified:           0
% 2.68/0.99  inst_num_eq_res_simplified:             0
% 2.68/0.99  inst_num_child_elim:                    0
% 2.68/0.99  inst_num_of_dismatching_blockings:      116
% 2.68/0.99  inst_num_of_non_proper_insts:           448
% 2.68/0.99  inst_num_of_duplicates:                 0
% 2.68/0.99  inst_inst_num_from_inst_to_res:         0
% 2.68/0.99  inst_dismatching_checking_time:         0.
% 2.68/0.99  
% 2.68/0.99  ------ Resolution
% 2.68/0.99  
% 2.68/0.99  res_num_of_clauses:                     0
% 2.68/0.99  res_num_in_passive:                     0
% 2.68/0.99  res_num_in_active:                      0
% 2.68/0.99  res_num_of_loops:                       137
% 2.68/0.99  res_forward_subset_subsumed:            46
% 2.68/0.99  res_backward_subset_subsumed:           4
% 2.68/0.99  res_forward_subsumed:                   0
% 2.68/0.99  res_backward_subsumed:                  0
% 2.68/0.99  res_forward_subsumption_resolution:     1
% 2.68/0.99  res_backward_subsumption_resolution:    0
% 2.68/0.99  res_clause_to_clause_subsumption:       135
% 2.68/0.99  res_orphan_elimination:                 0
% 2.68/0.99  res_tautology_del:                      87
% 2.68/0.99  res_num_eq_res_simplified:              0
% 2.68/0.99  res_num_sel_changes:                    0
% 2.68/0.99  res_moves_from_active_to_pass:          0
% 2.68/0.99  
% 2.68/0.99  ------ Superposition
% 2.68/0.99  
% 2.68/0.99  sup_time_total:                         0.
% 2.68/0.99  sup_time_generating:                    0.
% 2.68/0.99  sup_time_sim_full:                      0.
% 2.68/0.99  sup_time_sim_immed:                     0.
% 2.68/0.99  
% 2.68/0.99  sup_num_of_clauses:                     45
% 2.68/0.99  sup_num_in_active:                      29
% 2.68/0.99  sup_num_in_passive:                     16
% 2.68/0.99  sup_num_of_loops:                       64
% 2.68/0.99  sup_fw_superposition:                   24
% 2.68/0.99  sup_bw_superposition:                   27
% 2.68/0.99  sup_immediate_simplified:               33
% 2.68/0.99  sup_given_eliminated:                   0
% 2.68/0.99  comparisons_done:                       0
% 2.68/0.99  comparisons_avoided:                    2
% 2.68/0.99  
% 2.68/0.99  ------ Simplifications
% 2.68/0.99  
% 2.68/0.99  
% 2.68/0.99  sim_fw_subset_subsumed:                 4
% 2.68/0.99  sim_bw_subset_subsumed:                 2
% 2.68/0.99  sim_fw_subsumed:                        6
% 2.68/0.99  sim_bw_subsumed:                        0
% 2.68/0.99  sim_fw_subsumption_res:                 5
% 2.68/0.99  sim_bw_subsumption_res:                 2
% 2.68/0.99  sim_tautology_del:                      2
% 2.68/0.99  sim_eq_tautology_del:                   4
% 2.68/0.99  sim_eq_res_simp:                        3
% 2.68/0.99  sim_fw_demodulated:                     3
% 2.68/0.99  sim_bw_demodulated:                     34
% 2.68/0.99  sim_light_normalised:                   28
% 2.68/0.99  sim_joinable_taut:                      0
% 2.68/0.99  sim_joinable_simp:                      0
% 2.68/0.99  sim_ac_normalised:                      0
% 2.68/0.99  sim_smt_subsumption:                    0
% 2.68/0.99  
%------------------------------------------------------------------------------
