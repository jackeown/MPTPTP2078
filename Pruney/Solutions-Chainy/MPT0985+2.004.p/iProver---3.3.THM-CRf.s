%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:20 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  190 (4597 expanded)
%              Number of clauses        :  120 (1460 expanded)
%              Number of leaves         :   18 ( 897 expanded)
%              Depth                    :   24
%              Number of atoms          :  590 (24546 expanded)
%              Number of equality atoms :  256 (5012 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f42,plain,
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

fof(f43,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f41,plain,(
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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1895,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1899,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4341,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1899])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_103,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1399,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2186,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_2187,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2186])).

cnf(c_2189,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_2421,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2955,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_2956,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2955])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1897,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3142,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1895,c_1897])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3154,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3142,c_28])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1294,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0
    | k2_funct_1(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_1295,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_1294])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1307,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1295,c_11])).

cnf(c_1880,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_357,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_358,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_360,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_32])).

cnf(c_1892,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_2183,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2197,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1892,c_32,c_30,c_358,c_2183])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_343,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_344,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_346,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_32])).

cnf(c_1893,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_2201,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1893,c_32,c_30,c_344,c_2183])).

cnf(c_2241,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1880,c_2197,c_2201])).

cnf(c_3222,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3154,c_2241])).

cnf(c_3226,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3222])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2184,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2183])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2272,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2273,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2272])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_1264,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1263])).

cnf(c_17,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_317,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_17,c_15])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_17,c_15])).

cnf(c_322,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_321])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1099,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_22])).

cnf(c_1100,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1099])).

cnf(c_1104,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1100,c_0])).

cnf(c_1105,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1104])).

cnf(c_1271,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1264,c_1105])).

cnf(c_1882,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2088,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1882,c_3])).

cnf(c_1148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_27])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_1150,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_2557,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2088,c_33,c_35,c_103,c_1150,c_2184,c_2189,c_2273])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1177,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1177])).

cnf(c_1180,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_30])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1898,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3487,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1895,c_1898])).

cnf(c_3652,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1180,c_3487])).

cnf(c_4187,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3226,c_33,c_35,c_2184,c_2241,c_2273,c_2557,c_3154,c_3652])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1896,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3320,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_1896])).

cnf(c_3223,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3154,c_2201])).

cnf(c_3332,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3320,c_3223])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3111,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3112,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3111])).

cnf(c_4193,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3332,c_33,c_35,c_2184,c_2273,c_3112])).

cnf(c_4198,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3652,c_4193])).

cnf(c_4594,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4341,c_33,c_35,c_103,c_2184,c_2189,c_2241,c_2273,c_2557,c_2956,c_3154,c_3652,c_4198])).

cnf(c_1906,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1905,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2913,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1905])).

cnf(c_4599,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4594,c_2913])).

cnf(c_4636,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4599,c_4187])).

cnf(c_4652,plain,
    ( k1_relset_1(sK0,sK1,k1_xboole_0) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4599,c_1180])).

cnf(c_4788,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4652,c_33,c_35,c_2184,c_2241,c_2273,c_2557,c_3154,c_3652,c_4198])).

cnf(c_6323,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4636,c_4788])).

cnf(c_6324,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6323,c_3])).

cnf(c_4642,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4599,c_3223])).

cnf(c_5279,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4642,c_4788])).

cnf(c_5281,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5279,c_1896])).

cnf(c_5282,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5281,c_3])).

cnf(c_86,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_88,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_89,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_91,plain,
    ( v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_6,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_92,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_94,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_2175,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2177,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2175])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2176,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2179,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2176])).

cnf(c_5441,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5282,c_88,c_91,c_94,c_103,c_2177,c_2179])).

cnf(c_6326,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6324,c_5441])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.73/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.99  
% 2.73/0.99  ------  iProver source info
% 2.73/0.99  
% 2.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.99  git: non_committed_changes: false
% 2.73/0.99  git: last_make_outside_of_git: false
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     num_symb
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       true
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  ------ Parsing...
% 2.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.99  ------ Proving...
% 2.73/0.99  ------ Problem Properties 
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  clauses                                 33
% 2.73/0.99  conjectures                             3
% 2.73/0.99  EPR                                     4
% 2.73/0.99  Horn                                    26
% 2.73/0.99  unary                                   7
% 2.73/0.99  binary                                  7
% 2.73/0.99  lits                                    92
% 2.73/0.99  lits eq                                 38
% 2.73/0.99  fd_pure                                 0
% 2.73/0.99  fd_pseudo                               0
% 2.73/0.99  fd_cond                                 3
% 2.73/0.99  fd_pseudo_cond                          1
% 2.73/0.99  AC symbols                              0
% 2.73/0.99  
% 2.73/0.99  ------ Schedule dynamic 5 is on 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  Current options:
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     none
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       false
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ Proving...
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS status Theorem for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99   Resolution empty clause
% 2.73/0.99  
% 2.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  fof(f17,conjecture,(
% 2.73/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f18,negated_conjecture,(
% 2.73/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.73/0.99    inference(negated_conjecture,[],[f17])).
% 2.73/0.99  
% 2.73/0.99  fof(f37,plain,(
% 2.73/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.73/0.99    inference(ennf_transformation,[],[f18])).
% 2.73/0.99  
% 2.73/0.99  fof(f38,plain,(
% 2.73/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.73/0.99    inference(flattening,[],[f37])).
% 2.73/0.99  
% 2.73/0.99  fof(f42,plain,(
% 2.73/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f43,plain,(
% 2.73/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42])).
% 2.73/0.99  
% 2.73/0.99  fof(f73,plain,(
% 2.73/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f10,axiom,(
% 2.73/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f27,plain,(
% 2.73/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f10])).
% 2.73/0.99  
% 2.73/0.99  fof(f56,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f1,axiom,(
% 2.73/0.99    v1_xboole_0(k1_xboole_0)),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f44,plain,(
% 2.73/0.99    v1_xboole_0(k1_xboole_0)),
% 2.73/0.99    inference(cnf_transformation,[],[f1])).
% 2.73/0.99  
% 2.73/0.99  fof(f12,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f29,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f12])).
% 2.73/0.99  
% 2.73/0.99  fof(f58,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f29])).
% 2.73/0.99  
% 2.73/0.99  fof(f75,plain,(
% 2.73/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f16,axiom,(
% 2.73/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f35,plain,(
% 2.73/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f16])).
% 2.73/0.99  
% 2.73/0.99  fof(f36,plain,(
% 2.73/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/0.99    inference(flattening,[],[f35])).
% 2.73/0.99  
% 2.73/0.99  fof(f69,plain,(
% 2.73/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f76,plain,(
% 2.73/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f9,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f26,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f9])).
% 2.73/0.99  
% 2.73/0.99  fof(f55,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f26])).
% 2.73/0.99  
% 2.73/0.99  fof(f8,axiom,(
% 2.73/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f24,plain,(
% 2.73/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f8])).
% 2.73/0.99  
% 2.73/0.99  fof(f25,plain,(
% 2.73/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/0.99    inference(flattening,[],[f24])).
% 2.73/0.99  
% 2.73/0.99  fof(f54,plain,(
% 2.73/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f74,plain,(
% 2.73/0.99    v2_funct_1(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f71,plain,(
% 2.73/0.99    v1_funct_1(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f53,plain,(
% 2.73/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f7,axiom,(
% 2.73/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f22,plain,(
% 2.73/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f7])).
% 2.73/0.99  
% 2.73/0.99  fof(f23,plain,(
% 2.73/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/0.99    inference(flattening,[],[f22])).
% 2.73/0.99  
% 2.73/0.99  fof(f52,plain,(
% 2.73/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f23])).
% 2.73/0.99  
% 2.73/0.99  fof(f15,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f33,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f15])).
% 2.73/0.99  
% 2.73/0.99  fof(f34,plain,(
% 2.73/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(flattening,[],[f33])).
% 2.73/0.99  
% 2.73/0.99  fof(f41,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(nnf_transformation,[],[f34])).
% 2.73/0.99  
% 2.73/0.99  fof(f65,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f41])).
% 2.73/0.99  
% 2.73/0.99  fof(f82,plain,(
% 2.73/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.73/0.99    inference(equality_resolution,[],[f65])).
% 2.73/0.99  
% 2.73/0.99  fof(f14,axiom,(
% 2.73/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f32,plain,(
% 2.73/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f14])).
% 2.73/0.99  
% 2.73/0.99  fof(f61,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f32])).
% 2.73/0.99  
% 2.73/0.99  fof(f13,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f30,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f13])).
% 2.73/0.99  
% 2.73/0.99  fof(f31,plain,(
% 2.73/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(flattening,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f60,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f31])).
% 2.73/0.99  
% 2.73/0.99  fof(f63,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f41])).
% 2.73/0.99  
% 2.73/0.99  fof(f83,plain,(
% 2.73/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.73/0.99    inference(equality_resolution,[],[f63])).
% 2.73/0.99  
% 2.73/0.99  fof(f3,axiom,(
% 2.73/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f39,plain,(
% 2.73/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.73/0.99    inference(nnf_transformation,[],[f3])).
% 2.73/0.99  
% 2.73/0.99  fof(f40,plain,(
% 2.73/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.73/0.99    inference(flattening,[],[f39])).
% 2.73/0.99  
% 2.73/0.99  fof(f47,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.73/0.99    inference(cnf_transformation,[],[f40])).
% 2.73/0.99  
% 2.73/0.99  fof(f78,plain,(
% 2.73/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.73/0.99    inference(equality_resolution,[],[f47])).
% 2.73/0.99  
% 2.73/0.99  fof(f62,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f41])).
% 2.73/0.99  
% 2.73/0.99  fof(f72,plain,(
% 2.73/0.99    v1_funct_2(sK2,sK0,sK1)),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f11,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f28,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f11])).
% 2.73/0.99  
% 2.73/0.99  fof(f57,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f28])).
% 2.73/0.99  
% 2.73/0.99  fof(f70,plain,(
% 2.73/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f51,plain,(
% 2.73/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f23])).
% 2.73/0.99  
% 2.73/0.99  fof(f2,axiom,(
% 2.73/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f20,plain,(
% 2.73/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f2])).
% 2.73/0.99  
% 2.73/0.99  fof(f45,plain,(
% 2.73/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f20])).
% 2.73/0.99  
% 2.73/0.99  fof(f6,axiom,(
% 2.73/0.99    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f21,plain,(
% 2.73/0.99    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f6])).
% 2.73/0.99  
% 2.73/0.99  fof(f50,plain,(
% 2.73/0.99    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f21])).
% 2.73/0.99  
% 2.73/0.99  fof(f4,axiom,(
% 2.73/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f49,plain,(
% 2.73/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f4])).
% 2.73/0.99  
% 2.73/0.99  cnf(c_30,negated_conjecture,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.73/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1895,plain,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_12,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | ~ v1_xboole_0(X2)
% 2.73/0.99      | v1_xboole_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1899,plain,
% 2.73/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.73/0.99      | v1_xboole_0(X2) != iProver_top
% 2.73/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4341,plain,
% 2.73/0.99      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1895,c_1899]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_35,plain,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_0,plain,
% 2.73/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_103,plain,
% 2.73/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1399,plain,
% 2.73/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2186,plain,
% 2.73/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_1399]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2187,plain,
% 2.73/0.99      ( sK1 != X0
% 2.73/0.99      | v1_xboole_0(X0) != iProver_top
% 2.73/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2186]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2189,plain,
% 2.73/0.99      ( sK1 != k1_xboole_0
% 2.73/0.99      | v1_xboole_0(sK1) = iProver_top
% 2.73/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_2187]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2421,plain,
% 2.73/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/0.99      | ~ v1_xboole_0(X1)
% 2.73/0.99      | v1_xboole_0(sK2) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2955,plain,
% 2.73/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.73/0.99      | ~ v1_xboole_0(sK1)
% 2.73/0.99      | v1_xboole_0(sK2) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_2421]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2956,plain,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.73/0.99      | v1_xboole_0(sK1) != iProver_top
% 2.73/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2955]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_14,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1897,plain,
% 2.73/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.73/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3142,plain,
% 2.73/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1895,c_1897]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_28,negated_conjecture,
% 2.73/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.73/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3154,plain,
% 2.73/0.99      ( k2_relat_1(sK2) = sK1 ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_3142,c_28]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_25,plain,
% 2.73/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.73/0.99      | ~ v1_relat_1(X0)
% 2.73/0.99      | ~ v1_funct_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_27,negated_conjecture,
% 2.73/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.73/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1294,plain,
% 2.73/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | k1_relat_1(X0) != sK1
% 2.73/1.00      | k2_relat_1(X0) != sK0
% 2.73/1.00      | k2_funct_1(sK2) != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1295,plain,
% 2.73/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.73/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1294]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_11,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1307,plain,
% 2.73/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.73/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.73/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1295,c_11]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1880,plain,
% 2.73/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.73/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_9,plain,
% 2.73/1.00      ( ~ v2_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_29,negated_conjecture,
% 2.73/1.00      ( v2_funct_1(sK2) ),
% 2.73/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_357,plain,
% 2.73/1.00      ( ~ v1_relat_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.73/1.00      | sK2 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_358,plain,
% 2.73/1.00      ( ~ v1_relat_1(sK2)
% 2.73/1.00      | ~ v1_funct_1(sK2)
% 2.73/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_357]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_32,negated_conjecture,
% 2.73/1.00      ( v1_funct_1(sK2) ),
% 2.73/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_360,plain,
% 2.73/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_358,c_32]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1892,plain,
% 2.73/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.73/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2183,plain,
% 2.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.73/1.00      | v1_relat_1(sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2197,plain,
% 2.73/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1892,c_32,c_30,c_358,c_2183]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_10,plain,
% 2.73/1.00      ( ~ v2_funct_1(X0)
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_343,plain,
% 2.73/1.00      ( ~ v1_relat_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.73/1.00      | sK2 != X0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_344,plain,
% 2.73/1.00      ( ~ v1_relat_1(sK2)
% 2.73/1.00      | ~ v1_funct_1(sK2)
% 2.73/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_343]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_346,plain,
% 2.73/1.00      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_344,c_32]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1893,plain,
% 2.73/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.73/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2201,plain,
% 2.73/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_1893,c_32,c_30,c_344,c_2183]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2241,plain,
% 2.73/1.00      ( k1_relat_1(sK2) != sK0
% 2.73/1.00      | k2_relat_1(sK2) != sK1
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_1880,c_2197,c_2201]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3222,plain,
% 2.73/1.00      ( k1_relat_1(sK2) != sK0
% 2.73/1.00      | sK1 != sK1
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_3154,c_2241]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3226,plain,
% 2.73/1.00      ( k1_relat_1(sK2) != sK0
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(equality_resolution_simp,[status(thm)],[c_3222]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_33,plain,
% 2.73/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2184,plain,
% 2.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.73/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2183]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_7,plain,
% 2.73/1.00      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2272,plain,
% 2.73/1.00      ( ~ v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2273,plain,
% 2.73/1.00      ( v1_relat_1(sK2) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2272]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_20,plain,
% 2.73/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.73/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1263,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.73/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.73/1.00      | k2_funct_1(sK2) != X0
% 2.73/1.00      | sK0 != X1
% 2.73/1.00      | sK1 != k1_xboole_0 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1264,plain,
% 2.73/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.73/1.00      | sK1 != k1_xboole_0 ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1263]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_17,plain,
% 2.73/1.00      ( v1_partfun1(X0,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_xboole_0(X1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_15,plain,
% 2.73/1.00      ( v1_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ v1_partfun1(X0,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_funct_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_317,plain,
% 2.73/1.00      ( v1_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_xboole_0(X1) ),
% 2.73/1.00      inference(resolution,[status(thm)],[c_17,c_15]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_321,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | v1_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_xboole_0(X1) ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_317,c_17,c_15]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_322,plain,
% 2.73/1.00      ( v1_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_xboole_0(X1) ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_321]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_22,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.73/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1099,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_xboole_0(X1)
% 2.73/1.00      | X3 != X0
% 2.73/1.00      | X4 != X2
% 2.73/1.00      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 2.73/1.00      | k1_xboole_0 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_322,c_22]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1100,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.73/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1099]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1104,plain,
% 2.73/1.00      ( ~ v1_funct_1(X0)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.73/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1100,c_0]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1105,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.73/1.00      inference(renaming,[status(thm)],[c_1104]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1271,plain,
% 2.73/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | sK1 != k1_xboole_0 ),
% 2.73/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1264,c_1105]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1882,plain,
% 2.73/1.00      ( sK1 != k1_xboole_0
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3,plain,
% 2.73/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2088,plain,
% 2.73/1.00      ( sK1 != k1_xboole_0
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_1882,c_3]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1148,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ v1_funct_1(X0)
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | ~ v1_xboole_0(X1)
% 2.73/1.00      | k2_funct_1(sK2) != X0
% 2.73/1.00      | sK0 != X2
% 2.73/1.00      | sK1 != X1 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_322,c_27]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1149,plain,
% 2.73/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.73/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.73/1.00      | ~ v1_xboole_0(sK1) ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1148]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1150,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.73/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2557,plain,
% 2.73/1.00      ( sK1 != k1_xboole_0
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_2088,c_33,c_35,c_103,c_1150,c_2184,c_2189,c_2273]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_23,plain,
% 2.73/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.73/1.00      | k1_xboole_0 = X2 ),
% 2.73/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_31,negated_conjecture,
% 2.73/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.73/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1177,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.73/1.00      | sK0 != X1
% 2.73/1.00      | sK1 != X2
% 2.73/1.00      | sK2 != X0
% 2.73/1.00      | k1_xboole_0 = X2 ),
% 2.73/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1178,plain,
% 2.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.73/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.73/1.00      | k1_xboole_0 = sK1 ),
% 2.73/1.00      inference(unflattening,[status(thm)],[c_1177]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1180,plain,
% 2.73/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1178,c_30]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_13,plain,
% 2.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1898,plain,
% 2.73/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.73/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3487,plain,
% 2.73/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1895,c_1898]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3652,plain,
% 2.73/1.00      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1180,c_3487]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4187,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_3226,c_33,c_35,c_2184,c_2241,c_2273,c_2557,c_3154,c_3652]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_24,plain,
% 2.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.73/1.00      | ~ v1_relat_1(X0)
% 2.73/1.00      | ~ v1_funct_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1896,plain,
% 2.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.73/1.00      | v1_relat_1(X0) != iProver_top
% 2.73/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3320,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.73/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_2197,c_1896]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3223,plain,
% 2.73/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_3154,c_2201]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3332,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.73/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_3320,c_3223]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_8,plain,
% 2.73/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3111,plain,
% 2.73/1.00      ( v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) | ~ v1_funct_1(sK2) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_3112,plain,
% 2.73/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.73/1.00      | v1_relat_1(sK2) != iProver_top
% 2.73/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3111]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4193,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_3332,c_33,c_35,c_2184,c_2273,c_3112]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4198,plain,
% 2.73/1.00      ( sK1 = k1_xboole_0
% 2.73/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_3652,c_4193]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4594,plain,
% 2.73/1.00      ( v1_xboole_0(sK2) = iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_4341,c_33,c_35,c_103,c_2184,c_2189,c_2241,c_2273,c_2557,
% 2.73/1.00                 c_2956,c_3154,c_3652,c_4198]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1906,plain,
% 2.73/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1,plain,
% 2.73/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.73/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_1905,plain,
% 2.73/1.00      ( X0 = X1
% 2.73/1.00      | v1_xboole_0(X0) != iProver_top
% 2.73/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2913,plain,
% 2.73/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_1906,c_1905]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4599,plain,
% 2.73/1.00      ( sK2 = k1_xboole_0 ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_4594,c_2913]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4636,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4599,c_4187]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4652,plain,
% 2.73/1.00      ( k1_relset_1(sK0,sK1,k1_xboole_0) = sK0 | sK1 = k1_xboole_0 ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4599,c_1180]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4788,plain,
% 2.73/1.00      ( sK1 = k1_xboole_0 ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_4652,c_33,c_35,c_2184,c_2241,c_2273,c_2557,c_3154,c_3652,
% 2.73/1.00                 c_4198]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_6323,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4636,c_4788]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_6324,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_6323,c_3]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_4642,plain,
% 2.73/1.00      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK1 ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_4599,c_3223]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5279,plain,
% 2.73/1.00      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.73/1.00      inference(light_normalisation,[status(thm)],[c_4642,c_4788]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5281,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0))))) = iProver_top
% 2.73/1.00      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.73/1.00      inference(superposition,[status(thm)],[c_5279,c_1896]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5282,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.73/1.00      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.73/1.00      inference(demodulation,[status(thm)],[c_5281,c_3]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_86,plain,
% 2.73/1.00      ( v1_relat_1(X0) != iProver_top
% 2.73/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 2.73/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_88,plain,
% 2.73/1.00      ( v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.73/1.00      | v1_relat_1(k1_xboole_0) != iProver_top
% 2.73/1.00      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_86]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_89,plain,
% 2.73/1.00      ( v1_relat_1(X0) != iProver_top
% 2.73/1.00      | v1_funct_1(X0) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_91,plain,
% 2.73/1.00      ( v1_relat_1(k1_xboole_0) != iProver_top
% 2.73/1.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.73/1.00      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_89]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_6,plain,
% 2.73/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_92,plain,
% 2.73/1.00      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_94,plain,
% 2.73/1.00      ( v1_funct_1(k1_xboole_0) = iProver_top
% 2.73/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_92]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2175,plain,
% 2.73/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.00      | v1_relat_1(k1_xboole_0) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2177,plain,
% 2.73/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2175]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5,plain,
% 2.73/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.73/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2176,plain,
% 2.73/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.73/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_2179,plain,
% 2.73/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2176]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_5441,plain,
% 2.73/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.73/1.00      inference(global_propositional_subsumption,
% 2.73/1.00                [status(thm)],
% 2.73/1.00                [c_5282,c_88,c_91,c_94,c_103,c_2177,c_2179]) ).
% 2.73/1.00  
% 2.73/1.00  cnf(c_6326,plain,
% 2.73/1.00      ( $false ),
% 2.73/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6324,c_5441]) ).
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.00  
% 2.73/1.00  ------                               Statistics
% 2.73/1.00  
% 2.73/1.00  ------ General
% 2.73/1.00  
% 2.73/1.00  abstr_ref_over_cycles:                  0
% 2.73/1.00  abstr_ref_under_cycles:                 0
% 2.73/1.00  gc_basic_clause_elim:                   0
% 2.73/1.00  forced_gc_time:                         0
% 2.73/1.00  parsing_time:                           0.011
% 2.73/1.00  unif_index_cands_time:                  0.
% 2.73/1.00  unif_index_add_time:                    0.
% 2.73/1.00  orderings_time:                         0.
% 2.73/1.00  out_proof_time:                         0.01
% 2.73/1.00  total_time:                             0.196
% 2.73/1.00  num_of_symbols:                         49
% 2.73/1.00  num_of_terms:                           4899
% 2.73/1.00  
% 2.73/1.00  ------ Preprocessing
% 2.73/1.00  
% 2.73/1.00  num_of_splits:                          0
% 2.73/1.00  num_of_split_atoms:                     0
% 2.73/1.00  num_of_reused_defs:                     0
% 2.73/1.00  num_eq_ax_congr_red:                    4
% 2.73/1.00  num_of_sem_filtered_clauses:            1
% 2.73/1.00  num_of_subtypes:                        0
% 2.73/1.00  monotx_restored_types:                  0
% 2.73/1.00  sat_num_of_epr_types:                   0
% 2.73/1.00  sat_num_of_non_cyclic_types:            0
% 2.73/1.00  sat_guarded_non_collapsed_types:        0
% 2.73/1.00  num_pure_diseq_elim:                    0
% 2.73/1.00  simp_replaced_by:                       0
% 2.73/1.00  res_preprocessed:                       124
% 2.73/1.00  prep_upred:                             0
% 2.73/1.00  prep_unflattend:                        84
% 2.73/1.00  smt_new_axioms:                         0
% 2.73/1.00  pred_elim_cands:                        7
% 2.73/1.00  pred_elim:                              3
% 2.73/1.00  pred_elim_cl:                           -2
% 2.73/1.00  pred_elim_cycles:                       5
% 2.73/1.00  merged_defs:                            0
% 2.73/1.00  merged_defs_ncl:                        0
% 2.73/1.00  bin_hyper_res:                          0
% 2.73/1.00  prep_cycles:                            3
% 2.73/1.00  pred_elim_time:                         0.023
% 2.73/1.00  splitting_time:                         0.
% 2.73/1.00  sem_filter_time:                        0.
% 2.73/1.00  monotx_time:                            0.001
% 2.73/1.00  subtype_inf_time:                       0.
% 2.73/1.00  
% 2.73/1.00  ------ Problem properties
% 2.73/1.00  
% 2.73/1.00  clauses:                                33
% 2.73/1.00  conjectures:                            3
% 2.73/1.00  epr:                                    4
% 2.73/1.00  horn:                                   26
% 2.73/1.00  ground:                                 15
% 2.73/1.00  unary:                                  7
% 2.73/1.00  binary:                                 7
% 2.73/1.00  lits:                                   92
% 2.73/1.00  lits_eq:                                38
% 2.73/1.00  fd_pure:                                0
% 2.73/1.00  fd_pseudo:                              0
% 2.73/1.00  fd_cond:                                3
% 2.73/1.00  fd_pseudo_cond:                         1
% 2.73/1.00  ac_symbols:                             0
% 2.73/1.00  
% 2.73/1.00  ------ Propositional Solver
% 2.73/1.00  
% 2.73/1.00  prop_solver_calls:                      24
% 2.73/1.00  prop_fast_solver_calls:                 1093
% 2.73/1.00  smt_solver_calls:                       0
% 2.73/1.00  smt_fast_solver_calls:                  0
% 2.73/1.00  prop_num_of_clauses:                    2313
% 2.73/1.00  prop_preprocess_simplified:             7332
% 2.73/1.00  prop_fo_subsumed:                       33
% 2.73/1.00  prop_solver_time:                       0.
% 2.73/1.00  smt_solver_time:                        0.
% 2.73/1.00  smt_fast_solver_time:                   0.
% 2.73/1.00  prop_fast_solver_time:                  0.
% 2.73/1.00  prop_unsat_core_time:                   0.
% 2.73/1.00  
% 2.73/1.00  ------ QBF
% 2.73/1.00  
% 2.73/1.00  qbf_q_res:                              0
% 2.73/1.00  qbf_num_tautologies:                    0
% 2.73/1.00  qbf_prep_cycles:                        0
% 2.73/1.00  
% 2.73/1.00  ------ BMC1
% 2.73/1.00  
% 2.73/1.00  bmc1_current_bound:                     -1
% 2.73/1.00  bmc1_last_solved_bound:                 -1
% 2.73/1.00  bmc1_unsat_core_size:                   -1
% 2.73/1.00  bmc1_unsat_core_parents_size:           -1
% 2.73/1.00  bmc1_merge_next_fun:                    0
% 2.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.00  
% 2.73/1.00  ------ Instantiation
% 2.73/1.00  
% 2.73/1.00  inst_num_of_clauses:                    792
% 2.73/1.00  inst_num_in_passive:                    489
% 2.73/1.00  inst_num_in_active:                     302
% 2.73/1.00  inst_num_in_unprocessed:                1
% 2.73/1.00  inst_num_of_loops:                      360
% 2.73/1.00  inst_num_of_learning_restarts:          0
% 2.73/1.00  inst_num_moves_active_passive:          56
% 2.73/1.00  inst_lit_activity:                      0
% 2.73/1.00  inst_lit_activity_moves:                0
% 2.73/1.00  inst_num_tautologies:                   0
% 2.73/1.00  inst_num_prop_implied:                  0
% 2.73/1.00  inst_num_existing_simplified:           0
% 2.73/1.00  inst_num_eq_res_simplified:             0
% 2.73/1.00  inst_num_child_elim:                    0
% 2.73/1.00  inst_num_of_dismatching_blockings:      117
% 2.73/1.00  inst_num_of_non_proper_insts:           668
% 2.73/1.00  inst_num_of_duplicates:                 0
% 2.73/1.00  inst_inst_num_from_inst_to_res:         0
% 2.73/1.00  inst_dismatching_checking_time:         0.
% 2.73/1.00  
% 2.73/1.00  ------ Resolution
% 2.73/1.00  
% 2.73/1.00  res_num_of_clauses:                     0
% 2.73/1.00  res_num_in_passive:                     0
% 2.73/1.00  res_num_in_active:                      0
% 2.73/1.00  res_num_of_loops:                       127
% 2.73/1.00  res_forward_subset_subsumed:            21
% 2.73/1.00  res_backward_subset_subsumed:           2
% 2.73/1.00  res_forward_subsumed:                   2
% 2.73/1.00  res_backward_subsumed:                  0
% 2.73/1.00  res_forward_subsumption_resolution:     5
% 2.73/1.00  res_backward_subsumption_resolution:    0
% 2.73/1.00  res_clause_to_clause_subsumption:       171
% 2.73/1.00  res_orphan_elimination:                 0
% 2.73/1.00  res_tautology_del:                      64
% 2.73/1.00  res_num_eq_res_simplified:              0
% 2.73/1.00  res_num_sel_changes:                    0
% 2.73/1.00  res_moves_from_active_to_pass:          0
% 2.73/1.00  
% 2.73/1.00  ------ Superposition
% 2.73/1.00  
% 2.73/1.00  sup_time_total:                         0.
% 2.73/1.00  sup_time_generating:                    0.
% 2.73/1.00  sup_time_sim_full:                      0.
% 2.73/1.00  sup_time_sim_immed:                     0.
% 2.73/1.00  
% 2.73/1.00  sup_num_of_clauses:                     65
% 2.73/1.00  sup_num_in_active:                      43
% 2.73/1.00  sup_num_in_passive:                     22
% 2.73/1.00  sup_num_of_loops:                       71
% 2.73/1.00  sup_fw_superposition:                   41
% 2.73/1.00  sup_bw_superposition:                   31
% 2.73/1.00  sup_immediate_simplified:               29
% 2.73/1.00  sup_given_eliminated:                   1
% 2.73/1.00  comparisons_done:                       0
% 2.73/1.00  comparisons_avoided:                    10
% 2.73/1.00  
% 2.73/1.00  ------ Simplifications
% 2.73/1.00  
% 2.73/1.00  
% 2.73/1.00  sim_fw_subset_subsumed:                 7
% 2.73/1.00  sim_bw_subset_subsumed:                 3
% 2.73/1.00  sim_fw_subsumed:                        8
% 2.73/1.00  sim_bw_subsumed:                        4
% 2.73/1.00  sim_fw_subsumption_res:                 1
% 2.73/1.00  sim_bw_subsumption_res:                 0
% 2.73/1.00  sim_tautology_del:                      1
% 2.73/1.00  sim_eq_tautology_del:                   5
% 2.73/1.00  sim_eq_res_simp:                        1
% 2.73/1.00  sim_fw_demodulated:                     11
% 2.73/1.00  sim_bw_demodulated:                     28
% 2.73/1.00  sim_light_normalised:                   25
% 2.73/1.00  sim_joinable_taut:                      0
% 2.73/1.00  sim_joinable_simp:                      0
% 2.73/1.00  sim_ac_normalised:                      0
% 2.73/1.00  sim_smt_subsumption:                    0
% 2.73/1.00  
%------------------------------------------------------------------------------
