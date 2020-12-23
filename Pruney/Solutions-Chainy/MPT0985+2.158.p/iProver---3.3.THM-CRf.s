%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:52 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  155 (1803 expanded)
%              Number of clauses        :  100 ( 746 expanded)
%              Number of leaves         :   13 ( 306 expanded)
%              Depth                    :   19
%              Number of atoms          :  489 (8583 expanded)
%              Number of equality atoms :  260 (2119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f57,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k2_relat_1(X0) != k1_xboole_0 )
        & ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_xboole_0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_609,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1025,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_relat_1(X1_46)
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1013,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_1344,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1013])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_621,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1377,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1378,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_1439,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1344,c_1378])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_274,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_275,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_277,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_24])).

cnf(c_607,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_1027,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_1444,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1439,c_1027])).

cnf(c_13,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_299,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_300,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_606,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_300])).

cnf(c_1028,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_681,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_616,plain,
    ( ~ v1_funct_1(X0_46)
    | v1_funct_1(k2_funct_1(X0_46))
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1207,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_1208,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_1484,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_xboole_0 = sK1
    | sK0 != k1_xboole_0
    | k2_funct_1(sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1028,c_25,c_681,c_1208,c_1344,c_1378])).

cnf(c_1485,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1484])).

cnf(c_1563,plain,
    ( k4_relat_1(sK2) != k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1444,c_1485])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_378,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_602,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_378])).

cnf(c_1032,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_1564,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
    | sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1444,c_1032])).

cnf(c_1019,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(k2_funct_1(X0_46)) = iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_1729,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1444,c_1019])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_394,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_22])).

cnf(c_601,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1022,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_1906,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1025,c_1022])).

cnf(c_2012,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_601,c_1906])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_617,plain,
    ( ~ v1_relat_1(X0_46)
    | k1_relat_1(X0_46) != k1_xboole_0
    | k2_relat_1(X0_46) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1018,plain,
    ( k1_relat_1(X0_46) != k1_xboole_0
    | k2_relat_1(X0_46) = k1_xboole_0
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_2052,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_1018])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1023,plain,
    ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_1910,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1025,c_1023])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_610,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1911,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1910,c_610])).

cnf(c_2053,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2052,c_1911])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k3_relset_1(X1_46,X2_46,X0_46) = k4_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1024,plain,
    ( k3_relset_1(X0_46,X1_46,X2_46) = k4_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_2216,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1025,c_1024])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1021,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_2272,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2216,c_1021])).

cnf(c_2314,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2272,c_27])).

cnf(c_2322,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2314,c_1022])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_619,plain,
    ( ~ v1_relat_1(X0_46)
    | k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1016,plain,
    ( k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46)
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1445,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1439,c_1016])).

cnf(c_1949,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1911,c_1445])).

cnf(c_2324,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2322,c_1949])).

cnf(c_2384,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1563,c_25,c_27,c_1344,c_1378,c_1564,c_1729,c_2053,c_2272,c_2324])).

cnf(c_2387,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2384,c_2324])).

cnf(c_2388,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2384,c_2314])).

cnf(c_15,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_346,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_604,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1030,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_683,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_1494,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1030,c_25,c_683,c_1208,c_1344,c_1378])).

cnf(c_1495,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1494])).

cnf(c_1562,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1444,c_1495])).

cnf(c_2390,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2384,c_1562])).

cnf(c_2439,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2390])).

cnf(c_2448,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2388,c_2439])).

cnf(c_2459,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2387,c_2448])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:51:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.54/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/0.97  
% 2.54/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.54/0.97  
% 2.54/0.97  ------  iProver source info
% 2.54/0.97  
% 2.54/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.54/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.54/0.97  git: non_committed_changes: false
% 2.54/0.97  git: last_make_outside_of_git: false
% 2.54/0.97  
% 2.54/0.97  ------ 
% 2.54/0.97  
% 2.54/0.97  ------ Input Options
% 2.54/0.97  
% 2.54/0.97  --out_options                           all
% 2.54/0.97  --tptp_safe_out                         true
% 2.54/0.97  --problem_path                          ""
% 2.54/0.97  --include_path                          ""
% 2.54/0.97  --clausifier                            res/vclausify_rel
% 2.54/0.97  --clausifier_options                    --mode clausify
% 2.54/0.97  --stdin                                 false
% 2.54/0.97  --stats_out                             all
% 2.54/0.97  
% 2.54/0.97  ------ General Options
% 2.54/0.97  
% 2.54/0.97  --fof                                   false
% 2.54/0.97  --time_out_real                         305.
% 2.54/0.97  --time_out_virtual                      -1.
% 2.54/0.97  --symbol_type_check                     false
% 2.54/0.97  --clausify_out                          false
% 2.54/0.97  --sig_cnt_out                           false
% 2.54/0.97  --trig_cnt_out                          false
% 2.54/0.97  --trig_cnt_out_tolerance                1.
% 2.54/0.97  --trig_cnt_out_sk_spl                   false
% 2.54/0.97  --abstr_cl_out                          false
% 2.54/0.97  
% 2.54/0.97  ------ Global Options
% 2.54/0.97  
% 2.54/0.97  --schedule                              default
% 2.54/0.97  --add_important_lit                     false
% 2.54/0.97  --prop_solver_per_cl                    1000
% 2.54/0.97  --min_unsat_core                        false
% 2.54/0.97  --soft_assumptions                      false
% 2.54/0.97  --soft_lemma_size                       3
% 2.54/0.97  --prop_impl_unit_size                   0
% 2.54/0.97  --prop_impl_unit                        []
% 2.54/0.97  --share_sel_clauses                     true
% 2.54/0.97  --reset_solvers                         false
% 2.54/0.97  --bc_imp_inh                            [conj_cone]
% 2.54/0.97  --conj_cone_tolerance                   3.
% 2.54/0.97  --extra_neg_conj                        none
% 2.54/0.97  --large_theory_mode                     true
% 2.54/0.97  --prolific_symb_bound                   200
% 2.54/0.97  --lt_threshold                          2000
% 2.54/0.97  --clause_weak_htbl                      true
% 2.54/0.97  --gc_record_bc_elim                     false
% 2.54/0.97  
% 2.54/0.97  ------ Preprocessing Options
% 2.54/0.97  
% 2.54/0.97  --preprocessing_flag                    true
% 2.54/0.97  --time_out_prep_mult                    0.1
% 2.54/0.97  --splitting_mode                        input
% 2.54/0.97  --splitting_grd                         true
% 2.54/0.97  --splitting_cvd                         false
% 2.54/0.97  --splitting_cvd_svl                     false
% 2.54/0.97  --splitting_nvd                         32
% 2.54/0.97  --sub_typing                            true
% 2.54/0.97  --prep_gs_sim                           true
% 2.54/0.97  --prep_unflatten                        true
% 2.54/0.97  --prep_res_sim                          true
% 2.54/0.97  --prep_upred                            true
% 2.54/0.97  --prep_sem_filter                       exhaustive
% 2.54/0.97  --prep_sem_filter_out                   false
% 2.54/0.97  --pred_elim                             true
% 2.54/0.97  --res_sim_input                         true
% 2.54/0.97  --eq_ax_congr_red                       true
% 2.54/0.97  --pure_diseq_elim                       true
% 2.54/0.97  --brand_transform                       false
% 2.54/0.97  --non_eq_to_eq                          false
% 2.54/0.97  --prep_def_merge                        true
% 2.54/0.97  --prep_def_merge_prop_impl              false
% 2.54/0.97  --prep_def_merge_mbd                    true
% 2.54/0.97  --prep_def_merge_tr_red                 false
% 2.54/0.97  --prep_def_merge_tr_cl                  false
% 2.54/0.97  --smt_preprocessing                     true
% 2.54/0.97  --smt_ac_axioms                         fast
% 2.54/0.97  --preprocessed_out                      false
% 2.54/0.97  --preprocessed_stats                    false
% 2.54/0.97  
% 2.54/0.97  ------ Abstraction refinement Options
% 2.54/0.97  
% 2.54/0.97  --abstr_ref                             []
% 2.54/0.97  --abstr_ref_prep                        false
% 2.54/0.97  --abstr_ref_until_sat                   false
% 2.54/0.97  --abstr_ref_sig_restrict                funpre
% 2.54/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.54/0.97  --abstr_ref_under                       []
% 2.54/0.97  
% 2.54/0.97  ------ SAT Options
% 2.54/0.97  
% 2.54/0.97  --sat_mode                              false
% 2.54/0.97  --sat_fm_restart_options                ""
% 2.54/0.97  --sat_gr_def                            false
% 2.54/0.97  --sat_epr_types                         true
% 2.54/0.97  --sat_non_cyclic_types                  false
% 2.54/0.97  --sat_finite_models                     false
% 2.54/0.97  --sat_fm_lemmas                         false
% 2.54/0.97  --sat_fm_prep                           false
% 2.54/0.97  --sat_fm_uc_incr                        true
% 2.54/0.97  --sat_out_model                         small
% 2.54/0.97  --sat_out_clauses                       false
% 2.54/0.97  
% 2.54/0.97  ------ QBF Options
% 2.54/0.97  
% 2.54/0.97  --qbf_mode                              false
% 2.54/0.97  --qbf_elim_univ                         false
% 2.54/0.97  --qbf_dom_inst                          none
% 2.54/0.97  --qbf_dom_pre_inst                      false
% 2.54/0.97  --qbf_sk_in                             false
% 2.54/0.97  --qbf_pred_elim                         true
% 2.54/0.97  --qbf_split                             512
% 2.54/0.97  
% 2.54/0.97  ------ BMC1 Options
% 2.54/0.97  
% 2.54/0.97  --bmc1_incremental                      false
% 2.54/0.97  --bmc1_axioms                           reachable_all
% 2.54/0.97  --bmc1_min_bound                        0
% 2.54/0.97  --bmc1_max_bound                        -1
% 2.54/0.97  --bmc1_max_bound_default                -1
% 2.54/0.97  --bmc1_symbol_reachability              true
% 2.54/0.97  --bmc1_property_lemmas                  false
% 2.54/0.97  --bmc1_k_induction                      false
% 2.54/0.97  --bmc1_non_equiv_states                 false
% 2.54/0.97  --bmc1_deadlock                         false
% 2.54/0.97  --bmc1_ucm                              false
% 2.54/0.97  --bmc1_add_unsat_core                   none
% 2.54/0.97  --bmc1_unsat_core_children              false
% 2.54/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.54/0.97  --bmc1_out_stat                         full
% 2.54/0.97  --bmc1_ground_init                      false
% 2.54/0.97  --bmc1_pre_inst_next_state              false
% 2.54/0.97  --bmc1_pre_inst_state                   false
% 2.54/0.97  --bmc1_pre_inst_reach_state             false
% 2.54/0.97  --bmc1_out_unsat_core                   false
% 2.54/0.97  --bmc1_aig_witness_out                  false
% 2.54/0.97  --bmc1_verbose                          false
% 2.54/0.97  --bmc1_dump_clauses_tptp                false
% 2.54/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.54/0.97  --bmc1_dump_file                        -
% 2.54/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.54/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.54/0.97  --bmc1_ucm_extend_mode                  1
% 2.54/0.97  --bmc1_ucm_init_mode                    2
% 2.54/0.97  --bmc1_ucm_cone_mode                    none
% 2.54/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.54/0.97  --bmc1_ucm_relax_model                  4
% 2.54/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.54/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.54/0.97  --bmc1_ucm_layered_model                none
% 2.54/0.97  --bmc1_ucm_max_lemma_size               10
% 2.54/0.97  
% 2.54/0.97  ------ AIG Options
% 2.54/0.97  
% 2.54/0.97  --aig_mode                              false
% 2.54/0.97  
% 2.54/0.97  ------ Instantiation Options
% 2.54/0.97  
% 2.54/0.97  --instantiation_flag                    true
% 2.54/0.97  --inst_sos_flag                         false
% 2.54/0.97  --inst_sos_phase                        true
% 2.54/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.54/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.54/0.97  --inst_lit_sel_side                     num_symb
% 2.54/0.97  --inst_solver_per_active                1400
% 2.54/0.97  --inst_solver_calls_frac                1.
% 2.54/0.97  --inst_passive_queue_type               priority_queues
% 2.54/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.54/0.97  --inst_passive_queues_freq              [25;2]
% 2.54/0.97  --inst_dismatching                      true
% 2.54/0.97  --inst_eager_unprocessed_to_passive     true
% 2.54/0.97  --inst_prop_sim_given                   true
% 2.54/0.97  --inst_prop_sim_new                     false
% 2.54/0.97  --inst_subs_new                         false
% 2.54/0.97  --inst_eq_res_simp                      false
% 2.54/0.97  --inst_subs_given                       false
% 2.54/0.97  --inst_orphan_elimination               true
% 2.54/0.97  --inst_learning_loop_flag               true
% 2.54/0.97  --inst_learning_start                   3000
% 2.54/0.97  --inst_learning_factor                  2
% 2.54/0.97  --inst_start_prop_sim_after_learn       3
% 2.54/0.97  --inst_sel_renew                        solver
% 2.54/0.97  --inst_lit_activity_flag                true
% 2.54/0.97  --inst_restr_to_given                   false
% 2.54/0.97  --inst_activity_threshold               500
% 2.54/0.97  --inst_out_proof                        true
% 2.54/0.97  
% 2.54/0.97  ------ Resolution Options
% 2.54/0.97  
% 2.54/0.97  --resolution_flag                       true
% 2.54/0.97  --res_lit_sel                           adaptive
% 2.54/0.97  --res_lit_sel_side                      none
% 2.54/0.97  --res_ordering                          kbo
% 2.54/0.97  --res_to_prop_solver                    active
% 2.54/0.97  --res_prop_simpl_new                    false
% 2.54/0.97  --res_prop_simpl_given                  true
% 2.54/0.97  --res_passive_queue_type                priority_queues
% 2.54/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.54/0.97  --res_passive_queues_freq               [15;5]
% 2.54/0.97  --res_forward_subs                      full
% 2.54/0.97  --res_backward_subs                     full
% 2.54/0.97  --res_forward_subs_resolution           true
% 2.54/0.97  --res_backward_subs_resolution          true
% 2.54/0.97  --res_orphan_elimination                true
% 2.54/0.97  --res_time_limit                        2.
% 2.54/0.97  --res_out_proof                         true
% 2.54/0.97  
% 2.54/0.97  ------ Superposition Options
% 2.54/0.97  
% 2.54/0.97  --superposition_flag                    true
% 2.54/0.97  --sup_passive_queue_type                priority_queues
% 2.54/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.54/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.54/0.97  --demod_completeness_check              fast
% 2.54/0.97  --demod_use_ground                      true
% 2.54/0.97  --sup_to_prop_solver                    passive
% 2.54/0.97  --sup_prop_simpl_new                    true
% 2.54/0.97  --sup_prop_simpl_given                  true
% 2.54/0.97  --sup_fun_splitting                     false
% 2.54/0.97  --sup_smt_interval                      50000
% 2.54/0.97  
% 2.54/0.97  ------ Superposition Simplification Setup
% 2.54/0.97  
% 2.54/0.97  --sup_indices_passive                   []
% 2.54/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.54/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/0.97  --sup_full_bw                           [BwDemod]
% 2.54/0.97  --sup_immed_triv                        [TrivRules]
% 2.54/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.54/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/0.97  --sup_immed_bw_main                     []
% 2.54/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.54/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/0.97  
% 2.54/0.97  ------ Combination Options
% 2.54/0.97  
% 2.54/0.97  --comb_res_mult                         3
% 2.54/0.97  --comb_sup_mult                         2
% 2.54/0.97  --comb_inst_mult                        10
% 2.54/0.97  
% 2.54/0.97  ------ Debug Options
% 2.54/0.97  
% 2.54/0.97  --dbg_backtrace                         false
% 2.54/0.97  --dbg_dump_prop_clauses                 false
% 2.54/0.97  --dbg_dump_prop_clauses_file            -
% 2.54/0.97  --dbg_out_stat                          false
% 2.54/0.97  ------ Parsing...
% 2.54/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.54/0.97  
% 2.54/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.54/0.97  
% 2.54/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.54/0.97  
% 2.54/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.54/0.97  ------ Proving...
% 2.54/0.97  ------ Problem Properties 
% 2.54/0.97  
% 2.54/0.97  
% 2.54/0.97  clauses                                 23
% 2.54/0.97  conjectures                             3
% 2.54/0.97  EPR                                     1
% 2.54/0.97  Horn                                    21
% 2.54/0.97  unary                                   4
% 2.54/0.97  binary                                  8
% 2.54/0.97  lits                                    61
% 2.54/0.97  lits eq                                 27
% 2.54/0.97  fd_pure                                 0
% 2.54/0.97  fd_pseudo                               0
% 2.54/0.97  fd_cond                                 0
% 2.54/0.97  fd_pseudo_cond                          0
% 2.54/0.97  AC symbols                              0
% 2.54/0.97  
% 2.54/0.97  ------ Schedule dynamic 5 is on 
% 2.54/0.97  
% 2.54/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.54/0.97  
% 2.54/0.97  
% 2.54/0.97  ------ 
% 2.54/0.97  Current options:
% 2.54/0.97  ------ 
% 2.54/0.97  
% 2.54/0.97  ------ Input Options
% 2.54/0.97  
% 2.54/0.97  --out_options                           all
% 2.54/0.97  --tptp_safe_out                         true
% 2.54/0.97  --problem_path                          ""
% 2.54/0.97  --include_path                          ""
% 2.54/0.97  --clausifier                            res/vclausify_rel
% 2.54/0.97  --clausifier_options                    --mode clausify
% 2.54/0.97  --stdin                                 false
% 2.54/0.97  --stats_out                             all
% 2.54/0.97  
% 2.54/0.97  ------ General Options
% 2.54/0.97  
% 2.54/0.97  --fof                                   false
% 2.54/0.97  --time_out_real                         305.
% 2.54/0.97  --time_out_virtual                      -1.
% 2.54/0.97  --symbol_type_check                     false
% 2.54/0.97  --clausify_out                          false
% 2.54/0.97  --sig_cnt_out                           false
% 2.54/0.97  --trig_cnt_out                          false
% 2.54/0.97  --trig_cnt_out_tolerance                1.
% 2.54/0.97  --trig_cnt_out_sk_spl                   false
% 2.54/0.97  --abstr_cl_out                          false
% 2.54/0.97  
% 2.54/0.97  ------ Global Options
% 2.54/0.97  
% 2.54/0.97  --schedule                              default
% 2.54/0.97  --add_important_lit                     false
% 2.54/0.97  --prop_solver_per_cl                    1000
% 2.54/0.97  --min_unsat_core                        false
% 2.54/0.97  --soft_assumptions                      false
% 2.54/0.97  --soft_lemma_size                       3
% 2.54/0.97  --prop_impl_unit_size                   0
% 2.54/0.97  --prop_impl_unit                        []
% 2.54/0.97  --share_sel_clauses                     true
% 2.54/0.97  --reset_solvers                         false
% 2.54/0.97  --bc_imp_inh                            [conj_cone]
% 2.54/0.97  --conj_cone_tolerance                   3.
% 2.54/0.97  --extra_neg_conj                        none
% 2.54/0.97  --large_theory_mode                     true
% 2.54/0.97  --prolific_symb_bound                   200
% 2.54/0.97  --lt_threshold                          2000
% 2.54/0.97  --clause_weak_htbl                      true
% 2.54/0.97  --gc_record_bc_elim                     false
% 2.54/0.97  
% 2.54/0.97  ------ Preprocessing Options
% 2.54/0.97  
% 2.54/0.97  --preprocessing_flag                    true
% 2.54/0.97  --time_out_prep_mult                    0.1
% 2.54/0.97  --splitting_mode                        input
% 2.54/0.97  --splitting_grd                         true
% 2.54/0.97  --splitting_cvd                         false
% 2.54/0.97  --splitting_cvd_svl                     false
% 2.54/0.97  --splitting_nvd                         32
% 2.54/0.97  --sub_typing                            true
% 2.54/0.97  --prep_gs_sim                           true
% 2.54/0.97  --prep_unflatten                        true
% 2.54/0.97  --prep_res_sim                          true
% 2.54/0.97  --prep_upred                            true
% 2.54/0.97  --prep_sem_filter                       exhaustive
% 2.54/0.97  --prep_sem_filter_out                   false
% 2.54/0.97  --pred_elim                             true
% 2.54/0.97  --res_sim_input                         true
% 2.54/0.97  --eq_ax_congr_red                       true
% 2.54/0.97  --pure_diseq_elim                       true
% 2.54/0.97  --brand_transform                       false
% 2.54/0.97  --non_eq_to_eq                          false
% 2.54/0.97  --prep_def_merge                        true
% 2.54/0.97  --prep_def_merge_prop_impl              false
% 2.54/0.97  --prep_def_merge_mbd                    true
% 2.54/0.97  --prep_def_merge_tr_red                 false
% 2.54/0.97  --prep_def_merge_tr_cl                  false
% 2.54/0.97  --smt_preprocessing                     true
% 2.54/0.97  --smt_ac_axioms                         fast
% 2.54/0.97  --preprocessed_out                      false
% 2.54/0.97  --preprocessed_stats                    false
% 2.54/0.97  
% 2.54/0.97  ------ Abstraction refinement Options
% 2.54/0.97  
% 2.54/0.97  --abstr_ref                             []
% 2.54/0.97  --abstr_ref_prep                        false
% 2.54/0.97  --abstr_ref_until_sat                   false
% 2.54/0.97  --abstr_ref_sig_restrict                funpre
% 2.54/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.54/0.97  --abstr_ref_under                       []
% 2.54/0.97  
% 2.54/0.97  ------ SAT Options
% 2.54/0.97  
% 2.54/0.97  --sat_mode                              false
% 2.54/0.97  --sat_fm_restart_options                ""
% 2.54/0.97  --sat_gr_def                            false
% 2.54/0.97  --sat_epr_types                         true
% 2.54/0.97  --sat_non_cyclic_types                  false
% 2.54/0.97  --sat_finite_models                     false
% 2.54/0.97  --sat_fm_lemmas                         false
% 2.54/0.97  --sat_fm_prep                           false
% 2.54/0.97  --sat_fm_uc_incr                        true
% 2.54/0.97  --sat_out_model                         small
% 2.54/0.97  --sat_out_clauses                       false
% 2.54/0.97  
% 2.54/0.97  ------ QBF Options
% 2.54/0.97  
% 2.54/0.97  --qbf_mode                              false
% 2.54/0.97  --qbf_elim_univ                         false
% 2.54/0.97  --qbf_dom_inst                          none
% 2.54/0.97  --qbf_dom_pre_inst                      false
% 2.54/0.97  --qbf_sk_in                             false
% 2.54/0.97  --qbf_pred_elim                         true
% 2.54/0.97  --qbf_split                             512
% 2.54/0.97  
% 2.54/0.97  ------ BMC1 Options
% 2.54/0.97  
% 2.54/0.97  --bmc1_incremental                      false
% 2.54/0.97  --bmc1_axioms                           reachable_all
% 2.54/0.97  --bmc1_min_bound                        0
% 2.54/0.97  --bmc1_max_bound                        -1
% 2.54/0.97  --bmc1_max_bound_default                -1
% 2.54/0.97  --bmc1_symbol_reachability              true
% 2.54/0.97  --bmc1_property_lemmas                  false
% 2.54/0.97  --bmc1_k_induction                      false
% 2.54/0.97  --bmc1_non_equiv_states                 false
% 2.54/0.97  --bmc1_deadlock                         false
% 2.54/0.97  --bmc1_ucm                              false
% 2.54/0.97  --bmc1_add_unsat_core                   none
% 2.54/0.97  --bmc1_unsat_core_children              false
% 2.54/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.54/0.97  --bmc1_out_stat                         full
% 2.54/0.97  --bmc1_ground_init                      false
% 2.54/0.97  --bmc1_pre_inst_next_state              false
% 2.54/0.97  --bmc1_pre_inst_state                   false
% 2.54/0.97  --bmc1_pre_inst_reach_state             false
% 2.54/0.97  --bmc1_out_unsat_core                   false
% 2.54/0.97  --bmc1_aig_witness_out                  false
% 2.54/0.97  --bmc1_verbose                          false
% 2.54/0.97  --bmc1_dump_clauses_tptp                false
% 2.54/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.54/0.97  --bmc1_dump_file                        -
% 2.54/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.54/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.54/0.97  --bmc1_ucm_extend_mode                  1
% 2.54/0.97  --bmc1_ucm_init_mode                    2
% 2.54/0.97  --bmc1_ucm_cone_mode                    none
% 2.54/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.54/0.97  --bmc1_ucm_relax_model                  4
% 2.54/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.54/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.54/0.97  --bmc1_ucm_layered_model                none
% 2.54/0.97  --bmc1_ucm_max_lemma_size               10
% 2.54/0.97  
% 2.54/0.97  ------ AIG Options
% 2.54/0.97  
% 2.54/0.97  --aig_mode                              false
% 2.54/0.97  
% 2.54/0.97  ------ Instantiation Options
% 2.54/0.97  
% 2.54/0.97  --instantiation_flag                    true
% 2.54/0.97  --inst_sos_flag                         false
% 2.54/0.97  --inst_sos_phase                        true
% 2.54/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.54/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.54/0.97  --inst_lit_sel_side                     none
% 2.54/0.97  --inst_solver_per_active                1400
% 2.54/0.97  --inst_solver_calls_frac                1.
% 2.54/0.97  --inst_passive_queue_type               priority_queues
% 2.54/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.54/0.97  --inst_passive_queues_freq              [25;2]
% 2.54/0.97  --inst_dismatching                      true
% 2.54/0.97  --inst_eager_unprocessed_to_passive     true
% 2.54/0.97  --inst_prop_sim_given                   true
% 2.54/0.97  --inst_prop_sim_new                     false
% 2.54/0.97  --inst_subs_new                         false
% 2.54/0.97  --inst_eq_res_simp                      false
% 2.54/0.97  --inst_subs_given                       false
% 2.54/0.97  --inst_orphan_elimination               true
% 2.54/0.97  --inst_learning_loop_flag               true
% 2.54/0.97  --inst_learning_start                   3000
% 2.54/0.97  --inst_learning_factor                  2
% 2.54/0.97  --inst_start_prop_sim_after_learn       3
% 2.54/0.97  --inst_sel_renew                        solver
% 2.54/0.97  --inst_lit_activity_flag                true
% 2.54/0.97  --inst_restr_to_given                   false
% 2.54/0.97  --inst_activity_threshold               500
% 2.54/0.97  --inst_out_proof                        true
% 2.54/0.97  
% 2.54/0.97  ------ Resolution Options
% 2.54/0.97  
% 2.54/0.97  --resolution_flag                       false
% 2.54/0.97  --res_lit_sel                           adaptive
% 2.54/0.97  --res_lit_sel_side                      none
% 2.54/0.97  --res_ordering                          kbo
% 2.54/0.97  --res_to_prop_solver                    active
% 2.54/0.97  --res_prop_simpl_new                    false
% 2.54/0.97  --res_prop_simpl_given                  true
% 2.54/0.97  --res_passive_queue_type                priority_queues
% 2.54/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.54/0.97  --res_passive_queues_freq               [15;5]
% 2.54/0.97  --res_forward_subs                      full
% 2.54/0.97  --res_backward_subs                     full
% 2.54/0.97  --res_forward_subs_resolution           true
% 2.54/0.97  --res_backward_subs_resolution          true
% 2.54/0.97  --res_orphan_elimination                true
% 2.54/0.97  --res_time_limit                        2.
% 2.54/0.97  --res_out_proof                         true
% 2.54/0.97  
% 2.54/0.97  ------ Superposition Options
% 2.54/0.97  
% 2.54/0.97  --superposition_flag                    true
% 2.54/0.97  --sup_passive_queue_type                priority_queues
% 2.54/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.54/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.54/0.97  --demod_completeness_check              fast
% 2.54/0.97  --demod_use_ground                      true
% 2.54/0.97  --sup_to_prop_solver                    passive
% 2.54/0.97  --sup_prop_simpl_new                    true
% 2.54/0.97  --sup_prop_simpl_given                  true
% 2.54/0.97  --sup_fun_splitting                     false
% 2.54/0.97  --sup_smt_interval                      50000
% 2.54/0.97  
% 2.54/0.97  ------ Superposition Simplification Setup
% 2.54/0.97  
% 2.54/0.97  --sup_indices_passive                   []
% 2.54/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.54/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.54/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/0.97  --sup_full_bw                           [BwDemod]
% 2.54/0.97  --sup_immed_triv                        [TrivRules]
% 2.54/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.54/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/0.97  --sup_immed_bw_main                     []
% 2.54/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.54/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.54/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.54/0.97  
% 2.54/0.97  ------ Combination Options
% 2.54/0.97  
% 2.54/0.97  --comb_res_mult                         3
% 2.54/0.97  --comb_sup_mult                         2
% 2.54/0.97  --comb_inst_mult                        10
% 2.54/0.97  
% 2.54/0.97  ------ Debug Options
% 2.54/0.97  
% 2.54/0.97  --dbg_backtrace                         false
% 2.54/0.97  --dbg_dump_prop_clauses                 false
% 2.54/0.97  --dbg_dump_prop_clauses_file            -
% 2.54/0.97  --dbg_out_stat                          false
% 2.54/0.97  
% 2.54/0.97  
% 2.54/0.97  
% 2.54/0.97  
% 2.54/0.97  ------ Proving...
% 2.54/0.97  
% 2.54/0.97  
% 2.54/0.97  % SZS status Theorem for theBenchmark.p
% 2.54/0.97  
% 2.54/0.97   Resolution empty clause
% 2.54/0.97  
% 2.54/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.54/0.97  
% 2.54/0.97  fof(f12,conjecture,(
% 2.54/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.54/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.97  
% 2.54/0.97  fof(f13,negated_conjecture,(
% 2.54/0.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.54/0.97    inference(negated_conjecture,[],[f12])).
% 2.54/0.97  
% 2.54/0.97  fof(f27,plain,(
% 2.54/0.97    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.54/0.98    inference(ennf_transformation,[],[f13])).
% 2.54/0.98  
% 2.54/0.98  fof(f28,plain,(
% 2.54/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.54/0.98    inference(flattening,[],[f27])).
% 2.54/0.98  
% 2.54/0.98  fof(f31,plain,(
% 2.54/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.54/0.98    introduced(choice_axiom,[])).
% 2.54/0.98  
% 2.54/0.98  fof(f32,plain,(
% 2.54/0.98    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 2.54/0.98  
% 2.54/0.98  fof(f54,plain,(
% 2.54/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.54/0.98    inference(cnf_transformation,[],[f32])).
% 2.54/0.98  
% 2.54/0.98  fof(f1,axiom,(
% 2.54/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f14,plain,(
% 2.54/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.54/0.98    inference(ennf_transformation,[],[f1])).
% 2.54/0.98  
% 2.54/0.98  fof(f33,plain,(
% 2.54/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.54/0.98    inference(cnf_transformation,[],[f14])).
% 2.54/0.98  
% 2.54/0.98  fof(f2,axiom,(
% 2.54/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f34,plain,(
% 2.54/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f2])).
% 2.54/0.98  
% 2.54/0.98  fof(f5,axiom,(
% 2.54/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f17,plain,(
% 2.54/0.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.54/0.98    inference(ennf_transformation,[],[f5])).
% 2.54/0.98  
% 2.54/0.98  fof(f18,plain,(
% 2.54/0.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.54/0.98    inference(flattening,[],[f17])).
% 2.54/0.98  
% 2.54/0.98  fof(f39,plain,(
% 2.54/0.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.54/0.98    inference(cnf_transformation,[],[f18])).
% 2.54/0.98  
% 2.54/0.98  fof(f55,plain,(
% 2.54/0.98    v2_funct_1(sK2)),
% 2.54/0.98    inference(cnf_transformation,[],[f32])).
% 2.54/0.98  
% 2.54/0.98  fof(f52,plain,(
% 2.54/0.98    v1_funct_1(sK2)),
% 2.54/0.98    inference(cnf_transformation,[],[f32])).
% 2.54/0.98  
% 2.54/0.98  fof(f11,axiom,(
% 2.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f25,plain,(
% 2.54/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/0.98    inference(ennf_transformation,[],[f11])).
% 2.54/0.98  
% 2.54/0.98  fof(f26,plain,(
% 2.54/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/0.98    inference(flattening,[],[f25])).
% 2.54/0.98  
% 2.54/0.98  fof(f30,plain,(
% 2.54/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/0.98    inference(nnf_transformation,[],[f26])).
% 2.54/0.98  
% 2.54/0.98  fof(f51,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f30])).
% 2.54/0.98  
% 2.54/0.98  fof(f58,plain,(
% 2.54/0.98    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(equality_resolution,[],[f51])).
% 2.54/0.98  
% 2.54/0.98  fof(f59,plain,(
% 2.54/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.54/0.98    inference(equality_resolution,[],[f58])).
% 2.54/0.98  
% 2.54/0.98  fof(f57,plain,(
% 2.54/0.98    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.54/0.98    inference(cnf_transformation,[],[f32])).
% 2.54/0.98  
% 2.54/0.98  fof(f6,axiom,(
% 2.54/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f19,plain,(
% 2.54/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.54/0.98    inference(ennf_transformation,[],[f6])).
% 2.54/0.98  
% 2.54/0.98  fof(f20,plain,(
% 2.54/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.54/0.98    inference(flattening,[],[f19])).
% 2.54/0.98  
% 2.54/0.98  fof(f41,plain,(
% 2.54/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.54/0.98    inference(cnf_transformation,[],[f20])).
% 2.54/0.98  
% 2.54/0.98  fof(f48,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f30])).
% 2.54/0.98  
% 2.54/0.98  fof(f46,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f30])).
% 2.54/0.98  
% 2.54/0.98  fof(f53,plain,(
% 2.54/0.98    v1_funct_2(sK2,sK0,sK1)),
% 2.54/0.98    inference(cnf_transformation,[],[f32])).
% 2.54/0.98  
% 2.54/0.98  fof(f8,axiom,(
% 2.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f22,plain,(
% 2.54/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/0.98    inference(ennf_transformation,[],[f8])).
% 2.54/0.98  
% 2.54/0.98  fof(f43,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f22])).
% 2.54/0.98  
% 2.54/0.98  fof(f4,axiom,(
% 2.54/0.98    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f16,plain,(
% 2.54/0.98    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0) | ~v1_relat_1(X0))),
% 2.54/0.98    inference(ennf_transformation,[],[f4])).
% 2.54/0.98  
% 2.54/0.98  fof(f29,plain,(
% 2.54/0.98    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0) & (k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 2.54/0.98    inference(nnf_transformation,[],[f16])).
% 2.54/0.98  
% 2.54/0.98  fof(f37,plain,(
% 2.54/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 2.54/0.98    inference(cnf_transformation,[],[f29])).
% 2.54/0.98  
% 2.54/0.98  fof(f9,axiom,(
% 2.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f23,plain,(
% 2.54/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/0.98    inference(ennf_transformation,[],[f9])).
% 2.54/0.98  
% 2.54/0.98  fof(f44,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f23])).
% 2.54/0.98  
% 2.54/0.98  fof(f56,plain,(
% 2.54/0.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.54/0.98    inference(cnf_transformation,[],[f32])).
% 2.54/0.98  
% 2.54/0.98  fof(f10,axiom,(
% 2.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f24,plain,(
% 2.54/0.98    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/0.98    inference(ennf_transformation,[],[f10])).
% 2.54/0.98  
% 2.54/0.98  fof(f45,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f24])).
% 2.54/0.98  
% 2.54/0.98  fof(f7,axiom,(
% 2.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f21,plain,(
% 2.54/0.98    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.54/0.98    inference(ennf_transformation,[],[f7])).
% 2.54/0.98  
% 2.54/0.98  fof(f42,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f21])).
% 2.54/0.98  
% 2.54/0.98  fof(f3,axiom,(
% 2.54/0.98    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.54/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.54/0.98  
% 2.54/0.98  fof(f15,plain,(
% 2.54/0.98    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.54/0.98    inference(ennf_transformation,[],[f3])).
% 2.54/0.98  
% 2.54/0.98  fof(f35,plain,(
% 2.54/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.54/0.98    inference(cnf_transformation,[],[f15])).
% 2.54/0.98  
% 2.54/0.98  fof(f49,plain,(
% 2.54/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.54/0.98    inference(cnf_transformation,[],[f30])).
% 2.54/0.98  
% 2.54/0.98  fof(f61,plain,(
% 2.54/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.54/0.98    inference(equality_resolution,[],[f49])).
% 2.54/0.98  
% 2.54/0.98  cnf(c_22,negated_conjecture,
% 2.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.54/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_609,negated_conjecture,
% 2.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1025,plain,
% 2.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_0,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.54/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_622,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.54/0.98      | ~ v1_relat_1(X1_46)
% 2.54/0.98      | v1_relat_1(X0_46) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1013,plain,
% 2.54/0.98      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.54/0.98      | v1_relat_1(X1_46) != iProver_top
% 2.54/0.98      | v1_relat_1(X0_46) = iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1344,plain,
% 2.54/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.54/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_1025,c_1013]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1,plain,
% 2.54/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.54/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_621,plain,
% 2.54/0.98      ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1377,plain,
% 2.54/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.54/0.98      inference(instantiation,[status(thm)],[c_621]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1378,plain,
% 2.54/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_1377]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1439,plain,
% 2.54/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.54/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1344,c_1378]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_6,plain,
% 2.54/0.98      ( ~ v1_funct_1(X0)
% 2.54/0.98      | ~ v2_funct_1(X0)
% 2.54/0.98      | ~ v1_relat_1(X0)
% 2.54/0.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.54/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_21,negated_conjecture,
% 2.54/0.98      ( v2_funct_1(sK2) ),
% 2.54/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_274,plain,
% 2.54/0.98      ( ~ v1_funct_1(X0)
% 2.54/0.98      | ~ v1_relat_1(X0)
% 2.54/0.98      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.54/0.98      | sK2 != X0 ),
% 2.54/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_275,plain,
% 2.54/0.98      ( ~ v1_funct_1(sK2)
% 2.54/0.98      | ~ v1_relat_1(sK2)
% 2.54/0.98      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.54/0.98      inference(unflattening,[status(thm)],[c_274]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_24,negated_conjecture,
% 2.54/0.98      ( v1_funct_1(sK2) ),
% 2.54/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_277,plain,
% 2.54/0.98      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.54/0.98      inference(global_propositional_subsumption,[status(thm)],[c_275,c_24]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_607,plain,
% 2.54/0.98      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_277]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1027,plain,
% 2.54/0.98      ( k2_funct_1(sK2) = k4_relat_1(sK2) | v1_relat_1(sK2) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1444,plain,
% 2.54/0.98      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_1439,c_1027]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_13,plain,
% 2.54/0.98      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.54/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.54/0.98      | k1_xboole_0 = X0 ),
% 2.54/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_19,negated_conjecture,
% 2.54/0.98      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.54/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.54/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_299,plain,
% 2.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k2_funct_1(sK2) != k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | sK1 != X0
% 2.54/0.98      | k1_xboole_0 = X0 ),
% 2.54/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_300,plain,
% 2.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k2_funct_1(sK2) != k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | k1_xboole_0 = sK1 ),
% 2.54/0.98      inference(unflattening,[status(thm)],[c_299]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_606,plain,
% 2.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k2_funct_1(sK2) != k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | k1_xboole_0 = sK1 ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_300]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1028,plain,
% 2.54/0.98      ( k2_funct_1(sK2) != k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | k1_xboole_0 = sK1
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 2.54/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_25,plain,
% 2.54/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_681,plain,
% 2.54/0.98      ( k2_funct_1(sK2) != k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | k1_xboole_0 = sK1
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 2.54/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_7,plain,
% 2.54/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.54/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_616,plain,
% 2.54/0.98      ( ~ v1_funct_1(X0_46)
% 2.54/0.98      | v1_funct_1(k2_funct_1(X0_46))
% 2.54/0.98      | ~ v1_relat_1(X0_46) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1207,plain,
% 2.54/0.98      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.54/0.98      inference(instantiation,[status(thm)],[c_616]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1208,plain,
% 2.54/0.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.54/0.98      | v1_funct_1(sK2) != iProver_top
% 2.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1484,plain,
% 2.54/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | k1_xboole_0 = sK1
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | k2_funct_1(sK2) != k1_xboole_0 ),
% 2.54/0.98      inference(global_propositional_subsumption,
% 2.54/0.98                [status(thm)],
% 2.54/0.98                [c_1028,c_25,c_681,c_1208,c_1344,c_1378]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1485,plain,
% 2.54/0.98      ( k2_funct_1(sK2) != k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | k1_xboole_0 = sK1
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.54/0.98      inference(renaming,[status(thm)],[c_1484]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1563,plain,
% 2.54/0.98      ( k4_relat_1(sK2) != k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | sK1 = k1_xboole_0
% 2.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_1444,c_1485]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_27,plain,
% 2.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_16,plain,
% 2.54/0.98      ( v1_funct_2(X0,X1,X2)
% 2.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.54/0.98      | k1_xboole_0 = X2 ),
% 2.54/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_377,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.54/0.98      | k2_funct_1(sK2) != X0
% 2.54/0.98      | sK0 != X2
% 2.54/0.98      | sK1 != X1
% 2.54/0.98      | k1_xboole_0 = X2 ),
% 2.54/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_378,plain,
% 2.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.54/0.98      | k1_xboole_0 = sK0 ),
% 2.54/0.98      inference(unflattening,[status(thm)],[c_377]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_602,plain,
% 2.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.54/0.98      | k1_xboole_0 = sK0 ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_378]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1032,plain,
% 2.54/0.98      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.54/0.98      | k1_xboole_0 = sK0
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1564,plain,
% 2.54/0.98      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
% 2.54/0.98      | sK0 = k1_xboole_0
% 2.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_1444,c_1032]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1019,plain,
% 2.54/0.98      ( v1_funct_1(X0_46) != iProver_top
% 2.54/0.98      | v1_funct_1(k2_funct_1(X0_46)) = iProver_top
% 2.54/0.98      | v1_relat_1(X0_46) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1729,plain,
% 2.54/0.98      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.54/0.98      | v1_funct_1(sK2) != iProver_top
% 2.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_1444,c_1019]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_18,plain,
% 2.54/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.54/0.98      | k1_xboole_0 = X2 ),
% 2.54/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_23,negated_conjecture,
% 2.54/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.54/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_393,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.54/0.98      | sK0 != X1
% 2.54/0.98      | sK1 != X2
% 2.54/0.98      | sK2 != X0
% 2.54/0.98      | k1_xboole_0 = X2 ),
% 2.54/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_394,plain,
% 2.54/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.54/0.98      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.54/0.98      | k1_xboole_0 = sK1 ),
% 2.54/0.98      inference(unflattening,[status(thm)],[c_393]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_396,plain,
% 2.54/0.98      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.54/0.98      inference(global_propositional_subsumption,[status(thm)],[c_394,c_22]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_601,plain,
% 2.54/0.98      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_396]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_10,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.54/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_613,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.54/0.98      | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1022,plain,
% 2.54/0.98      ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
% 2.54/0.98      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1906,plain,
% 2.54/0.98      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_1025,c_1022]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2012,plain,
% 2.54/0.98      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_601,c_1906]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_5,plain,
% 2.54/0.98      ( ~ v1_relat_1(X0)
% 2.54/0.98      | k1_relat_1(X0) != k1_xboole_0
% 2.54/0.98      | k2_relat_1(X0) = k1_xboole_0 ),
% 2.54/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_617,plain,
% 2.54/0.98      ( ~ v1_relat_1(X0_46)
% 2.54/0.98      | k1_relat_1(X0_46) != k1_xboole_0
% 2.54/0.98      | k2_relat_1(X0_46) = k1_xboole_0 ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1018,plain,
% 2.54/0.98      ( k1_relat_1(X0_46) != k1_xboole_0
% 2.54/0.98      | k2_relat_1(X0_46) = k1_xboole_0
% 2.54/0.98      | v1_relat_1(X0_46) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2052,plain,
% 2.54/0.98      ( k2_relat_1(sK2) = k1_xboole_0
% 2.54/0.98      | sK0 != k1_xboole_0
% 2.54/0.98      | sK1 = k1_xboole_0
% 2.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_2012,c_1018]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_11,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.54/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_612,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.54/0.98      | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1023,plain,
% 2.54/0.98      ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
% 2.54/0.98      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1910,plain,
% 2.54/0.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_1025,c_1023]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_20,negated_conjecture,
% 2.54/0.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.54/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_610,negated_conjecture,
% 2.54/0.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1911,plain,
% 2.54/0.98      ( k2_relat_1(sK2) = sK1 ),
% 2.54/0.98      inference(light_normalisation,[status(thm)],[c_1910,c_610]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2053,plain,
% 2.54/0.98      ( sK0 != k1_xboole_0
% 2.54/0.98      | sK1 = k1_xboole_0
% 2.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_2052,c_1911]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_12,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.54/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_611,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.54/0.98      | k3_relset_1(X1_46,X2_46,X0_46) = k4_relat_1(X0_46) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1024,plain,
% 2.54/0.98      ( k3_relset_1(X0_46,X1_46,X2_46) = k4_relat_1(X2_46)
% 2.54/0.98      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2216,plain,
% 2.54/0.98      ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_1025,c_1024]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_9,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.54/0.98      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.54/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_614,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.54/0.98      | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1021,plain,
% 2.54/0.98      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 2.54/0.98      | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) = iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2272,plain,
% 2.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 2.54/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_2216,c_1021]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2314,plain,
% 2.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.54/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2272,c_27]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2322,plain,
% 2.54/0.98      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_2314,c_1022]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_3,plain,
% 2.54/0.98      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.54/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_619,plain,
% 2.54/0.98      ( ~ v1_relat_1(X0_46)
% 2.54/0.98      | k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46) ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1016,plain,
% 2.54/0.98      ( k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46)
% 2.54/0.98      | v1_relat_1(X0_46) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1445,plain,
% 2.54/0.98      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.54/0.98      inference(superposition,[status(thm)],[c_1439,c_1016]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1949,plain,
% 2.54/0.98      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_1911,c_1445]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2324,plain,
% 2.54/0.98      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
% 2.54/0.98      inference(light_normalisation,[status(thm)],[c_2322,c_1949]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2384,plain,
% 2.54/0.98      ( sK1 = k1_xboole_0 ),
% 2.54/0.98      inference(global_propositional_subsumption,
% 2.54/0.98                [status(thm)],
% 2.54/0.98                [c_1563,c_25,c_27,c_1344,c_1378,c_1564,c_1729,c_2053,c_2272,
% 2.54/0.98                 c_2324]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2387,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) = k1_xboole_0 ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_2384,c_2324]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2388,plain,
% 2.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_2384,c_2314]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_15,plain,
% 2.54/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.54/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.54/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_345,plain,
% 2.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.54/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.54/0.98      | k2_funct_1(sK2) != X0
% 2.54/0.98      | sK0 != X1
% 2.54/0.98      | sK1 != k1_xboole_0 ),
% 2.54/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_346,plain,
% 2.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.54/0.98      | sK1 != k1_xboole_0 ),
% 2.54/0.98      inference(unflattening,[status(thm)],[c_345]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_604,plain,
% 2.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.54/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.54/0.98      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.54/0.98      | sK1 != k1_xboole_0 ),
% 2.54/0.98      inference(subtyping,[status(esa)],[c_346]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1030,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.54/0.98      | sK1 != k1_xboole_0
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.54/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_683,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.54/0.98      | sK1 != k1_xboole_0
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.54/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.54/0.98      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1494,plain,
% 2.54/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | sK1 != k1_xboole_0
% 2.54/0.98      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.54/0.98      inference(global_propositional_subsumption,
% 2.54/0.98                [status(thm)],
% 2.54/0.98                [c_1030,c_25,c_683,c_1208,c_1344,c_1378]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1495,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.54/0.98      | sK1 != k1_xboole_0
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.54/0.98      inference(renaming,[status(thm)],[c_1494]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_1562,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 2.54/0.98      | sK1 != k1_xboole_0
% 2.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_1444,c_1495]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2390,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 2.54/0.98      | k1_xboole_0 != k1_xboole_0
% 2.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.54/0.98      inference(demodulation,[status(thm)],[c_2384,c_1562]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2439,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 2.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.54/0.98      inference(equality_resolution_simp,[status(thm)],[c_2390]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2448,plain,
% 2.54/0.98      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0 ),
% 2.54/0.98      inference(backward_subsumption_resolution,[status(thm)],[c_2388,c_2439]) ).
% 2.54/0.98  
% 2.54/0.98  cnf(c_2459,plain,
% 2.54/0.98      ( $false ),
% 2.54/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2387,c_2448]) ).
% 2.54/0.98  
% 2.54/0.98  
% 2.54/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.54/0.98  
% 2.54/0.98  ------                               Statistics
% 2.54/0.98  
% 2.54/0.98  ------ General
% 2.54/0.98  
% 2.54/0.98  abstr_ref_over_cycles:                  0
% 2.54/0.98  abstr_ref_under_cycles:                 0
% 2.54/0.98  gc_basic_clause_elim:                   0
% 2.54/0.98  forced_gc_time:                         0
% 2.54/0.98  parsing_time:                           0.008
% 2.54/0.98  unif_index_cands_time:                  0.
% 2.54/0.98  unif_index_add_time:                    0.
% 2.54/0.98  orderings_time:                         0.
% 2.54/0.98  out_proof_time:                         0.013
% 2.54/0.98  total_time:                             0.109
% 2.54/0.98  num_of_symbols:                         51
% 2.54/0.98  num_of_terms:                           1926
% 2.54/0.98  
% 2.54/0.98  ------ Preprocessing
% 2.54/0.98  
% 2.54/0.98  num_of_splits:                          0
% 2.54/0.98  num_of_split_atoms:                     0
% 2.54/0.98  num_of_reused_defs:                     0
% 2.54/0.98  num_eq_ax_congr_red:                    12
% 2.54/0.98  num_of_sem_filtered_clauses:            1
% 2.54/0.98  num_of_subtypes:                        2
% 2.54/0.98  monotx_restored_types:                  0
% 2.54/0.98  sat_num_of_epr_types:                   0
% 2.54/0.98  sat_num_of_non_cyclic_types:            0
% 2.54/0.98  sat_guarded_non_collapsed_types:        0
% 2.54/0.98  num_pure_diseq_elim:                    0
% 2.54/0.98  simp_replaced_by:                       0
% 2.54/0.98  res_preprocessed:                       123
% 2.54/0.98  prep_upred:                             0
% 2.54/0.98  prep_unflattend:                        34
% 2.54/0.98  smt_new_axioms:                         0
% 2.54/0.98  pred_elim_cands:                        3
% 2.54/0.98  pred_elim:                              2
% 2.54/0.98  pred_elim_cl:                           2
% 2.54/0.98  pred_elim_cycles:                       4
% 2.54/0.98  merged_defs:                            0
% 2.54/0.98  merged_defs_ncl:                        0
% 2.54/0.98  bin_hyper_res:                          0
% 2.54/0.98  prep_cycles:                            4
% 2.54/0.98  pred_elim_time:                         0.004
% 2.54/0.98  splitting_time:                         0.
% 2.54/0.98  sem_filter_time:                        0.
% 2.54/0.98  monotx_time:                            0.
% 2.54/0.98  subtype_inf_time:                       0.
% 2.54/0.98  
% 2.54/0.98  ------ Problem properties
% 2.54/0.98  
% 2.54/0.98  clauses:                                23
% 2.54/0.98  conjectures:                            3
% 2.54/0.98  epr:                                    1
% 2.54/0.98  horn:                                   21
% 2.54/0.98  ground:                                 11
% 2.54/0.98  unary:                                  4
% 2.54/0.98  binary:                                 8
% 2.54/0.98  lits:                                   61
% 2.54/0.98  lits_eq:                                27
% 2.54/0.98  fd_pure:                                0
% 2.54/0.98  fd_pseudo:                              0
% 2.54/0.98  fd_cond:                                0
% 2.54/0.98  fd_pseudo_cond:                         0
% 2.54/0.98  ac_symbols:                             0
% 2.54/0.98  
% 2.54/0.98  ------ Propositional Solver
% 2.54/0.98  
% 2.54/0.98  prop_solver_calls:                      27
% 2.54/0.98  prop_fast_solver_calls:                 789
% 2.54/0.98  smt_solver_calls:                       0
% 2.54/0.98  smt_fast_solver_calls:                  0
% 2.54/0.98  prop_num_of_clauses:                    739
% 2.54/0.98  prop_preprocess_simplified:             3536
% 2.54/0.98  prop_fo_subsumed:                       13
% 2.54/0.98  prop_solver_time:                       0.
% 2.54/0.98  smt_solver_time:                        0.
% 2.54/0.98  smt_fast_solver_time:                   0.
% 2.54/0.98  prop_fast_solver_time:                  0.
% 2.54/0.98  prop_unsat_core_time:                   0.
% 2.54/0.98  
% 2.54/0.98  ------ QBF
% 2.54/0.98  
% 2.54/0.98  qbf_q_res:                              0
% 2.54/0.98  qbf_num_tautologies:                    0
% 2.54/0.98  qbf_prep_cycles:                        0
% 2.54/0.98  
% 2.54/0.98  ------ BMC1
% 2.54/0.98  
% 2.54/0.98  bmc1_current_bound:                     -1
% 2.54/0.98  bmc1_last_solved_bound:                 -1
% 2.54/0.98  bmc1_unsat_core_size:                   -1
% 2.54/0.98  bmc1_unsat_core_parents_size:           -1
% 2.54/0.98  bmc1_merge_next_fun:                    0
% 2.54/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.54/0.98  
% 2.54/0.98  ------ Instantiation
% 2.54/0.98  
% 2.54/0.98  inst_num_of_clauses:                    262
% 2.54/0.98  inst_num_in_passive:                    24
% 2.54/0.98  inst_num_in_active:                     186
% 2.54/0.98  inst_num_in_unprocessed:                52
% 2.54/0.98  inst_num_of_loops:                      210
% 2.54/0.98  inst_num_of_learning_restarts:          0
% 2.54/0.98  inst_num_moves_active_passive:          21
% 2.54/0.98  inst_lit_activity:                      0
% 2.54/0.98  inst_lit_activity_moves:                0
% 2.54/0.98  inst_num_tautologies:                   0
% 2.54/0.98  inst_num_prop_implied:                  0
% 2.54/0.98  inst_num_existing_simplified:           0
% 2.54/0.98  inst_num_eq_res_simplified:             0
% 2.54/0.98  inst_num_child_elim:                    0
% 2.54/0.98  inst_num_of_dismatching_blockings:      25
% 2.54/0.98  inst_num_of_non_proper_insts:           194
% 2.54/0.98  inst_num_of_duplicates:                 0
% 2.54/0.98  inst_inst_num_from_inst_to_res:         0
% 2.54/0.98  inst_dismatching_checking_time:         0.
% 2.54/0.98  
% 2.54/0.98  ------ Resolution
% 2.54/0.98  
% 2.54/0.98  res_num_of_clauses:                     0
% 2.54/0.98  res_num_in_passive:                     0
% 2.54/0.98  res_num_in_active:                      0
% 2.54/0.98  res_num_of_loops:                       127
% 2.54/0.98  res_forward_subset_subsumed:            30
% 2.54/0.98  res_backward_subset_subsumed:           2
% 2.54/0.98  res_forward_subsumed:                   0
% 2.54/0.98  res_backward_subsumed:                  0
% 2.54/0.98  res_forward_subsumption_resolution:     0
% 2.54/0.98  res_backward_subsumption_resolution:    0
% 2.54/0.98  res_clause_to_clause_subsumption:       81
% 2.54/0.98  res_orphan_elimination:                 0
% 2.54/0.98  res_tautology_del:                      56
% 2.54/0.98  res_num_eq_res_simplified:              0
% 2.54/0.98  res_num_sel_changes:                    0
% 2.54/0.98  res_moves_from_active_to_pass:          0
% 2.54/0.98  
% 2.54/0.98  ------ Superposition
% 2.54/0.98  
% 2.54/0.98  sup_time_total:                         0.
% 2.54/0.98  sup_time_generating:                    0.
% 2.54/0.98  sup_time_sim_full:                      0.
% 2.54/0.98  sup_time_sim_immed:                     0.
% 2.54/0.98  
% 2.54/0.98  sup_num_of_clauses:                     36
% 2.54/0.98  sup_num_in_active:                      19
% 2.54/0.98  sup_num_in_passive:                     17
% 2.54/0.98  sup_num_of_loops:                       41
% 2.54/0.98  sup_fw_superposition:                   11
% 2.54/0.98  sup_bw_superposition:                   20
% 2.54/0.98  sup_immediate_simplified:               8
% 2.54/0.98  sup_given_eliminated:                   0
% 2.54/0.98  comparisons_done:                       0
% 2.54/0.98  comparisons_avoided:                    5
% 2.54/0.98  
% 2.54/0.98  ------ Simplifications
% 2.54/0.98  
% 2.54/0.98  
% 2.54/0.98  sim_fw_subset_subsumed:                 0
% 2.54/0.98  sim_bw_subset_subsumed:                 2
% 2.54/0.98  sim_fw_subsumed:                        0
% 2.54/0.98  sim_bw_subsumed:                        0
% 2.54/0.98  sim_fw_subsumption_res:                 2
% 2.54/0.98  sim_bw_subsumption_res:                 2
% 2.54/0.98  sim_tautology_del:                      0
% 2.54/0.98  sim_eq_tautology_del:                   2
% 2.54/0.98  sim_eq_res_simp:                        3
% 2.54/0.98  sim_fw_demodulated:                     5
% 2.54/0.98  sim_bw_demodulated:                     22
% 2.54/0.98  sim_light_normalised:                   3
% 2.54/0.98  sim_joinable_taut:                      0
% 2.54/0.98  sim_joinable_simp:                      0
% 2.54/0.98  sim_ac_normalised:                      0
% 2.54/0.98  sim_smt_subsumption:                    0
% 2.54/0.98  
%------------------------------------------------------------------------------
