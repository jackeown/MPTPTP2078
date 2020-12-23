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
% DateTime   : Thu Dec  3 12:02:28 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  188 (2834 expanded)
%              Number of clauses        :  122 ( 977 expanded)
%              Number of leaves         :   17 ( 530 expanded)
%              Depth                    :   24
%              Number of atoms          :  572 (14960 expanded)
%              Number of equality atoms :  221 (2666 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_14,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_338,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_339,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_353,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_339])).

cnf(c_354,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_354,c_26])).

cnf(c_620,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_962,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_988,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sP0_iProver_split
    | sK1 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_962])).

cnf(c_1509,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_988])).

cnf(c_987,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_962])).

cnf(c_1510,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_1664,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1509,c_1510])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1054,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_988])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_985,plain,
    ( ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1749,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_1750,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_983,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1752,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_1753,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1752])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_516,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_29])).

cnf(c_967,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_976,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1496,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1492,plain,
    ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_1994,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1496,c_1492])).

cnf(c_2071,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_967,c_1994])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_672,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0
    | k2_funct_1(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_673,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_685,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_673,c_9])).

cnf(c_959,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(subtyping,[status(esa)],[c_685])).

cnf(c_1513,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_1060,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_3432,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_32,c_34,c_1060,c_1750,c_1753])).

cnf(c_3433,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3432])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_418,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_28])).

cnf(c_419,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_421,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_31])).

cnf(c_971,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1501,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_1767,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1501,c_29,c_971,c_1752])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_390,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_391,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_393,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_31])).

cnf(c_973,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_1499,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_1804,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1499,c_29,c_973,c_1752])).

cnf(c_1806,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1804,c_1767])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_980,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1493,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_2420,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1496,c_1493])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_977,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2427,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2420,c_977])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_376,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_377,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_379,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_31])).

cnf(c_974,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_1498,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_1799,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1498,c_29,c_974,c_1752])).

cnf(c_1801,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1799,c_1767])).

cnf(c_2433,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2427,c_1801])).

cnf(c_3436,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3433,c_1767,c_1806,c_2433])).

cnf(c_3437,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3436])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k3_relset_1(X1_48,X2_48,X0_48) = k4_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1494,plain,
    ( k3_relset_1(X0_48,X1_48,X2_48) = k4_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_2527,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1496,c_1494])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_982,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1491,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_2692,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_1491])).

cnf(c_2847,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_34])).

cnf(c_3440,plain,
    ( k1_relat_1(sK2) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3437,c_2847])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_978,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_48),k2_relat_1(X0_48))))
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1495,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_48),k2_relat_1(X0_48)))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_2543,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2427,c_1495])).

cnf(c_2744,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2543,c_32,c_34,c_1753])).

cnf(c_2751,plain,
    ( k3_relset_1(k1_relat_1(sK2),sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2744,c_1494])).

cnf(c_2800,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2751,c_1491])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k4_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_404,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k4_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_405,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_406,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_986,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(k4_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1813,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_1819,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_2688,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k4_relat_1(sK2))))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_1495])).

cnf(c_2689,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2688,c_1806])).

cnf(c_3955,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2800,c_32,c_34,c_406,c_1753,c_1819,c_2689])).

cnf(c_3441,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2071,c_3440])).

cnf(c_3959,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3955,c_3441])).

cnf(c_2074,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1510,c_1767])).

cnf(c_3969,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3959,c_2074])).

cnf(c_4154,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_32,c_34,c_1054,c_1750,c_1753,c_2071,c_3440,c_3969])).

cnf(c_4155,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4154])).

cnf(c_4158,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4155,c_1767,c_3441])).

cnf(c_3445,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3441,c_2847])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4158,c_3445])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:40:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.33/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.98  
% 2.33/0.98  ------  iProver source info
% 2.33/0.98  
% 2.33/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.98  git: non_committed_changes: false
% 2.33/0.98  git: last_make_outside_of_git: false
% 2.33/0.98  
% 2.33/0.98  ------ 
% 2.33/0.98  
% 2.33/0.98  ------ Input Options
% 2.33/0.98  
% 2.33/0.98  --out_options                           all
% 2.33/0.98  --tptp_safe_out                         true
% 2.33/0.98  --problem_path                          ""
% 2.33/0.98  --include_path                          ""
% 2.33/0.98  --clausifier                            res/vclausify_rel
% 2.33/0.98  --clausifier_options                    --mode clausify
% 2.33/0.98  --stdin                                 false
% 2.33/0.98  --stats_out                             all
% 2.33/0.98  
% 2.33/0.98  ------ General Options
% 2.33/0.98  
% 2.33/0.98  --fof                                   false
% 2.33/0.98  --time_out_real                         305.
% 2.33/0.98  --time_out_virtual                      -1.
% 2.33/0.98  --symbol_type_check                     false
% 2.33/0.98  --clausify_out                          false
% 2.33/0.98  --sig_cnt_out                           false
% 2.33/0.98  --trig_cnt_out                          false
% 2.33/0.98  --trig_cnt_out_tolerance                1.
% 2.33/0.98  --trig_cnt_out_sk_spl                   false
% 2.33/0.98  --abstr_cl_out                          false
% 2.33/0.98  
% 2.33/0.98  ------ Global Options
% 2.33/0.98  
% 2.33/0.98  --schedule                              default
% 2.33/0.98  --add_important_lit                     false
% 2.33/0.98  --prop_solver_per_cl                    1000
% 2.33/0.98  --min_unsat_core                        false
% 2.33/0.98  --soft_assumptions                      false
% 2.33/0.98  --soft_lemma_size                       3
% 2.33/0.98  --prop_impl_unit_size                   0
% 2.33/0.98  --prop_impl_unit                        []
% 2.33/0.98  --share_sel_clauses                     true
% 2.33/0.98  --reset_solvers                         false
% 2.33/0.98  --bc_imp_inh                            [conj_cone]
% 2.33/0.98  --conj_cone_tolerance                   3.
% 2.33/0.98  --extra_neg_conj                        none
% 2.33/0.98  --large_theory_mode                     true
% 2.33/0.98  --prolific_symb_bound                   200
% 2.33/0.98  --lt_threshold                          2000
% 2.33/0.98  --clause_weak_htbl                      true
% 2.33/0.98  --gc_record_bc_elim                     false
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing Options
% 2.33/0.98  
% 2.33/0.98  --preprocessing_flag                    true
% 2.33/0.98  --time_out_prep_mult                    0.1
% 2.33/0.98  --splitting_mode                        input
% 2.33/0.98  --splitting_grd                         true
% 2.33/0.98  --splitting_cvd                         false
% 2.33/0.98  --splitting_cvd_svl                     false
% 2.33/0.98  --splitting_nvd                         32
% 2.33/0.98  --sub_typing                            true
% 2.33/0.98  --prep_gs_sim                           true
% 2.33/0.98  --prep_unflatten                        true
% 2.33/0.98  --prep_res_sim                          true
% 2.33/0.98  --prep_upred                            true
% 2.33/0.98  --prep_sem_filter                       exhaustive
% 2.33/0.98  --prep_sem_filter_out                   false
% 2.33/0.98  --pred_elim                             true
% 2.33/0.98  --res_sim_input                         true
% 2.33/0.98  --eq_ax_congr_red                       true
% 2.33/0.98  --pure_diseq_elim                       true
% 2.33/0.98  --brand_transform                       false
% 2.33/0.98  --non_eq_to_eq                          false
% 2.33/0.98  --prep_def_merge                        true
% 2.33/0.98  --prep_def_merge_prop_impl              false
% 2.33/0.98  --prep_def_merge_mbd                    true
% 2.33/0.98  --prep_def_merge_tr_red                 false
% 2.33/0.98  --prep_def_merge_tr_cl                  false
% 2.33/0.98  --smt_preprocessing                     true
% 2.33/0.98  --smt_ac_axioms                         fast
% 2.33/0.98  --preprocessed_out                      false
% 2.33/0.98  --preprocessed_stats                    false
% 2.33/0.98  
% 2.33/0.98  ------ Abstraction refinement Options
% 2.33/0.98  
% 2.33/0.98  --abstr_ref                             []
% 2.33/0.98  --abstr_ref_prep                        false
% 2.33/0.98  --abstr_ref_until_sat                   false
% 2.33/0.98  --abstr_ref_sig_restrict                funpre
% 2.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.98  --abstr_ref_under                       []
% 2.33/0.98  
% 2.33/0.98  ------ SAT Options
% 2.33/0.98  
% 2.33/0.98  --sat_mode                              false
% 2.33/0.98  --sat_fm_restart_options                ""
% 2.33/0.98  --sat_gr_def                            false
% 2.33/0.98  --sat_epr_types                         true
% 2.33/0.98  --sat_non_cyclic_types                  false
% 2.33/0.98  --sat_finite_models                     false
% 2.33/0.98  --sat_fm_lemmas                         false
% 2.33/0.98  --sat_fm_prep                           false
% 2.33/0.98  --sat_fm_uc_incr                        true
% 2.33/0.98  --sat_out_model                         small
% 2.33/0.98  --sat_out_clauses                       false
% 2.33/0.98  
% 2.33/0.98  ------ QBF Options
% 2.33/0.98  
% 2.33/0.98  --qbf_mode                              false
% 2.33/0.98  --qbf_elim_univ                         false
% 2.33/0.98  --qbf_dom_inst                          none
% 2.33/0.98  --qbf_dom_pre_inst                      false
% 2.33/0.98  --qbf_sk_in                             false
% 2.33/0.98  --qbf_pred_elim                         true
% 2.33/0.98  --qbf_split                             512
% 2.33/0.98  
% 2.33/0.98  ------ BMC1 Options
% 2.33/0.98  
% 2.33/0.98  --bmc1_incremental                      false
% 2.33/0.98  --bmc1_axioms                           reachable_all
% 2.33/0.98  --bmc1_min_bound                        0
% 2.33/0.98  --bmc1_max_bound                        -1
% 2.33/0.98  --bmc1_max_bound_default                -1
% 2.33/0.98  --bmc1_symbol_reachability              true
% 2.33/0.98  --bmc1_property_lemmas                  false
% 2.33/0.98  --bmc1_k_induction                      false
% 2.33/0.98  --bmc1_non_equiv_states                 false
% 2.33/0.98  --bmc1_deadlock                         false
% 2.33/0.98  --bmc1_ucm                              false
% 2.33/0.98  --bmc1_add_unsat_core                   none
% 2.33/0.98  --bmc1_unsat_core_children              false
% 2.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.98  --bmc1_out_stat                         full
% 2.33/0.98  --bmc1_ground_init                      false
% 2.33/0.98  --bmc1_pre_inst_next_state              false
% 2.33/0.98  --bmc1_pre_inst_state                   false
% 2.33/0.98  --bmc1_pre_inst_reach_state             false
% 2.33/0.98  --bmc1_out_unsat_core                   false
% 2.33/0.98  --bmc1_aig_witness_out                  false
% 2.33/0.98  --bmc1_verbose                          false
% 2.33/0.98  --bmc1_dump_clauses_tptp                false
% 2.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.98  --bmc1_dump_file                        -
% 2.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.98  --bmc1_ucm_extend_mode                  1
% 2.33/0.98  --bmc1_ucm_init_mode                    2
% 2.33/0.98  --bmc1_ucm_cone_mode                    none
% 2.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.98  --bmc1_ucm_relax_model                  4
% 2.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.98  --bmc1_ucm_layered_model                none
% 2.33/0.98  --bmc1_ucm_max_lemma_size               10
% 2.33/0.98  
% 2.33/0.98  ------ AIG Options
% 2.33/0.98  
% 2.33/0.98  --aig_mode                              false
% 2.33/0.98  
% 2.33/0.98  ------ Instantiation Options
% 2.33/0.98  
% 2.33/0.98  --instantiation_flag                    true
% 2.33/0.98  --inst_sos_flag                         false
% 2.33/0.98  --inst_sos_phase                        true
% 2.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel_side                     num_symb
% 2.33/0.98  --inst_solver_per_active                1400
% 2.33/0.98  --inst_solver_calls_frac                1.
% 2.33/0.98  --inst_passive_queue_type               priority_queues
% 2.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.98  --inst_passive_queues_freq              [25;2]
% 2.33/0.98  --inst_dismatching                      true
% 2.33/0.98  --inst_eager_unprocessed_to_passive     true
% 2.33/0.98  --inst_prop_sim_given                   true
% 2.33/0.98  --inst_prop_sim_new                     false
% 2.33/0.98  --inst_subs_new                         false
% 2.33/0.98  --inst_eq_res_simp                      false
% 2.33/0.98  --inst_subs_given                       false
% 2.33/0.98  --inst_orphan_elimination               true
% 2.33/0.98  --inst_learning_loop_flag               true
% 2.33/0.98  --inst_learning_start                   3000
% 2.33/0.98  --inst_learning_factor                  2
% 2.33/0.98  --inst_start_prop_sim_after_learn       3
% 2.33/0.98  --inst_sel_renew                        solver
% 2.33/0.98  --inst_lit_activity_flag                true
% 2.33/0.98  --inst_restr_to_given                   false
% 2.33/0.98  --inst_activity_threshold               500
% 2.33/0.98  --inst_out_proof                        true
% 2.33/0.98  
% 2.33/0.98  ------ Resolution Options
% 2.33/0.98  
% 2.33/0.98  --resolution_flag                       true
% 2.33/0.98  --res_lit_sel                           adaptive
% 2.33/0.98  --res_lit_sel_side                      none
% 2.33/0.98  --res_ordering                          kbo
% 2.33/0.98  --res_to_prop_solver                    active
% 2.33/0.98  --res_prop_simpl_new                    false
% 2.33/0.98  --res_prop_simpl_given                  true
% 2.33/0.98  --res_passive_queue_type                priority_queues
% 2.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.98  --res_passive_queues_freq               [15;5]
% 2.33/0.98  --res_forward_subs                      full
% 2.33/0.98  --res_backward_subs                     full
% 2.33/0.98  --res_forward_subs_resolution           true
% 2.33/0.98  --res_backward_subs_resolution          true
% 2.33/0.98  --res_orphan_elimination                true
% 2.33/0.98  --res_time_limit                        2.
% 2.33/0.98  --res_out_proof                         true
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Options
% 2.33/0.98  
% 2.33/0.98  --superposition_flag                    true
% 2.33/0.98  --sup_passive_queue_type                priority_queues
% 2.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.98  --demod_completeness_check              fast
% 2.33/0.98  --demod_use_ground                      true
% 2.33/0.98  --sup_to_prop_solver                    passive
% 2.33/0.98  --sup_prop_simpl_new                    true
% 2.33/0.98  --sup_prop_simpl_given                  true
% 2.33/0.98  --sup_fun_splitting                     false
% 2.33/0.98  --sup_smt_interval                      50000
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Simplification Setup
% 2.33/0.98  
% 2.33/0.98  --sup_indices_passive                   []
% 2.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_full_bw                           [BwDemod]
% 2.33/0.98  --sup_immed_triv                        [TrivRules]
% 2.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_immed_bw_main                     []
% 2.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  
% 2.33/0.98  ------ Combination Options
% 2.33/0.98  
% 2.33/0.98  --comb_res_mult                         3
% 2.33/0.98  --comb_sup_mult                         2
% 2.33/0.98  --comb_inst_mult                        10
% 2.33/0.98  
% 2.33/0.98  ------ Debug Options
% 2.33/0.98  
% 2.33/0.98  --dbg_backtrace                         false
% 2.33/0.98  --dbg_dump_prop_clauses                 false
% 2.33/0.98  --dbg_dump_prop_clauses_file            -
% 2.33/0.98  --dbg_out_stat                          false
% 2.33/0.98  ------ Parsing...
% 2.33/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.98  ------ Proving...
% 2.33/0.98  ------ Problem Properties 
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  clauses                                 30
% 2.33/0.98  conjectures                             3
% 2.33/0.98  EPR                                     1
% 2.33/0.98  Horn                                    26
% 2.33/0.98  unary                                   3
% 2.33/0.98  binary                                  12
% 2.33/0.98  lits                                    88
% 2.33/0.98  lits eq                                 34
% 2.33/0.98  fd_pure                                 0
% 2.33/0.98  fd_pseudo                               0
% 2.33/0.98  fd_cond                                 1
% 2.33/0.98  fd_pseudo_cond                          0
% 2.33/0.98  AC symbols                              0
% 2.33/0.98  
% 2.33/0.98  ------ Schedule dynamic 5 is on 
% 2.33/0.98  
% 2.33/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  ------ 
% 2.33/0.98  Current options:
% 2.33/0.98  ------ 
% 2.33/0.98  
% 2.33/0.98  ------ Input Options
% 2.33/0.98  
% 2.33/0.98  --out_options                           all
% 2.33/0.98  --tptp_safe_out                         true
% 2.33/0.98  --problem_path                          ""
% 2.33/0.98  --include_path                          ""
% 2.33/0.98  --clausifier                            res/vclausify_rel
% 2.33/0.98  --clausifier_options                    --mode clausify
% 2.33/0.98  --stdin                                 false
% 2.33/0.98  --stats_out                             all
% 2.33/0.98  
% 2.33/0.98  ------ General Options
% 2.33/0.98  
% 2.33/0.98  --fof                                   false
% 2.33/0.98  --time_out_real                         305.
% 2.33/0.98  --time_out_virtual                      -1.
% 2.33/0.98  --symbol_type_check                     false
% 2.33/0.98  --clausify_out                          false
% 2.33/0.98  --sig_cnt_out                           false
% 2.33/0.98  --trig_cnt_out                          false
% 2.33/0.98  --trig_cnt_out_tolerance                1.
% 2.33/0.98  --trig_cnt_out_sk_spl                   false
% 2.33/0.98  --abstr_cl_out                          false
% 2.33/0.98  
% 2.33/0.98  ------ Global Options
% 2.33/0.98  
% 2.33/0.98  --schedule                              default
% 2.33/0.98  --add_important_lit                     false
% 2.33/0.98  --prop_solver_per_cl                    1000
% 2.33/0.98  --min_unsat_core                        false
% 2.33/0.98  --soft_assumptions                      false
% 2.33/0.98  --soft_lemma_size                       3
% 2.33/0.98  --prop_impl_unit_size                   0
% 2.33/0.98  --prop_impl_unit                        []
% 2.33/0.98  --share_sel_clauses                     true
% 2.33/0.98  --reset_solvers                         false
% 2.33/0.98  --bc_imp_inh                            [conj_cone]
% 2.33/0.98  --conj_cone_tolerance                   3.
% 2.33/0.98  --extra_neg_conj                        none
% 2.33/0.98  --large_theory_mode                     true
% 2.33/0.98  --prolific_symb_bound                   200
% 2.33/0.98  --lt_threshold                          2000
% 2.33/0.98  --clause_weak_htbl                      true
% 2.33/0.98  --gc_record_bc_elim                     false
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing Options
% 2.33/0.98  
% 2.33/0.98  --preprocessing_flag                    true
% 2.33/0.98  --time_out_prep_mult                    0.1
% 2.33/0.98  --splitting_mode                        input
% 2.33/0.98  --splitting_grd                         true
% 2.33/0.98  --splitting_cvd                         false
% 2.33/0.98  --splitting_cvd_svl                     false
% 2.33/0.98  --splitting_nvd                         32
% 2.33/0.98  --sub_typing                            true
% 2.33/0.98  --prep_gs_sim                           true
% 2.33/0.98  --prep_unflatten                        true
% 2.33/0.98  --prep_res_sim                          true
% 2.33/0.98  --prep_upred                            true
% 2.33/0.98  --prep_sem_filter                       exhaustive
% 2.33/0.98  --prep_sem_filter_out                   false
% 2.33/0.98  --pred_elim                             true
% 2.33/0.98  --res_sim_input                         true
% 2.33/0.98  --eq_ax_congr_red                       true
% 2.33/0.98  --pure_diseq_elim                       true
% 2.33/0.98  --brand_transform                       false
% 2.33/0.98  --non_eq_to_eq                          false
% 2.33/0.98  --prep_def_merge                        true
% 2.33/0.98  --prep_def_merge_prop_impl              false
% 2.33/0.98  --prep_def_merge_mbd                    true
% 2.33/0.98  --prep_def_merge_tr_red                 false
% 2.33/0.98  --prep_def_merge_tr_cl                  false
% 2.33/0.98  --smt_preprocessing                     true
% 2.33/0.98  --smt_ac_axioms                         fast
% 2.33/0.98  --preprocessed_out                      false
% 2.33/0.98  --preprocessed_stats                    false
% 2.33/0.98  
% 2.33/0.98  ------ Abstraction refinement Options
% 2.33/0.98  
% 2.33/0.98  --abstr_ref                             []
% 2.33/0.98  --abstr_ref_prep                        false
% 2.33/0.98  --abstr_ref_until_sat                   false
% 2.33/0.98  --abstr_ref_sig_restrict                funpre
% 2.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.98  --abstr_ref_under                       []
% 2.33/0.98  
% 2.33/0.98  ------ SAT Options
% 2.33/0.98  
% 2.33/0.98  --sat_mode                              false
% 2.33/0.98  --sat_fm_restart_options                ""
% 2.33/0.98  --sat_gr_def                            false
% 2.33/0.98  --sat_epr_types                         true
% 2.33/0.98  --sat_non_cyclic_types                  false
% 2.33/0.98  --sat_finite_models                     false
% 2.33/0.98  --sat_fm_lemmas                         false
% 2.33/0.98  --sat_fm_prep                           false
% 2.33/0.98  --sat_fm_uc_incr                        true
% 2.33/0.98  --sat_out_model                         small
% 2.33/0.98  --sat_out_clauses                       false
% 2.33/0.98  
% 2.33/0.98  ------ QBF Options
% 2.33/0.98  
% 2.33/0.98  --qbf_mode                              false
% 2.33/0.98  --qbf_elim_univ                         false
% 2.33/0.98  --qbf_dom_inst                          none
% 2.33/0.98  --qbf_dom_pre_inst                      false
% 2.33/0.98  --qbf_sk_in                             false
% 2.33/0.98  --qbf_pred_elim                         true
% 2.33/0.98  --qbf_split                             512
% 2.33/0.98  
% 2.33/0.98  ------ BMC1 Options
% 2.33/0.98  
% 2.33/0.98  --bmc1_incremental                      false
% 2.33/0.98  --bmc1_axioms                           reachable_all
% 2.33/0.98  --bmc1_min_bound                        0
% 2.33/0.98  --bmc1_max_bound                        -1
% 2.33/0.98  --bmc1_max_bound_default                -1
% 2.33/0.98  --bmc1_symbol_reachability              true
% 2.33/0.98  --bmc1_property_lemmas                  false
% 2.33/0.98  --bmc1_k_induction                      false
% 2.33/0.98  --bmc1_non_equiv_states                 false
% 2.33/0.98  --bmc1_deadlock                         false
% 2.33/0.98  --bmc1_ucm                              false
% 2.33/0.98  --bmc1_add_unsat_core                   none
% 2.33/0.98  --bmc1_unsat_core_children              false
% 2.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.98  --bmc1_out_stat                         full
% 2.33/0.98  --bmc1_ground_init                      false
% 2.33/0.98  --bmc1_pre_inst_next_state              false
% 2.33/0.98  --bmc1_pre_inst_state                   false
% 2.33/0.98  --bmc1_pre_inst_reach_state             false
% 2.33/0.98  --bmc1_out_unsat_core                   false
% 2.33/0.98  --bmc1_aig_witness_out                  false
% 2.33/0.98  --bmc1_verbose                          false
% 2.33/0.98  --bmc1_dump_clauses_tptp                false
% 2.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.98  --bmc1_dump_file                        -
% 2.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.98  --bmc1_ucm_extend_mode                  1
% 2.33/0.98  --bmc1_ucm_init_mode                    2
% 2.33/0.98  --bmc1_ucm_cone_mode                    none
% 2.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.98  --bmc1_ucm_relax_model                  4
% 2.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.98  --bmc1_ucm_layered_model                none
% 2.33/0.98  --bmc1_ucm_max_lemma_size               10
% 2.33/0.98  
% 2.33/0.98  ------ AIG Options
% 2.33/0.98  
% 2.33/0.98  --aig_mode                              false
% 2.33/0.98  
% 2.33/0.98  ------ Instantiation Options
% 2.33/0.98  
% 2.33/0.98  --instantiation_flag                    true
% 2.33/0.98  --inst_sos_flag                         false
% 2.33/0.98  --inst_sos_phase                        true
% 2.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel_side                     none
% 2.33/0.98  --inst_solver_per_active                1400
% 2.33/0.98  --inst_solver_calls_frac                1.
% 2.33/0.98  --inst_passive_queue_type               priority_queues
% 2.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.98  --inst_passive_queues_freq              [25;2]
% 2.33/0.98  --inst_dismatching                      true
% 2.33/0.98  --inst_eager_unprocessed_to_passive     true
% 2.33/0.98  --inst_prop_sim_given                   true
% 2.33/0.98  --inst_prop_sim_new                     false
% 2.33/0.98  --inst_subs_new                         false
% 2.33/0.98  --inst_eq_res_simp                      false
% 2.33/0.98  --inst_subs_given                       false
% 2.33/0.98  --inst_orphan_elimination               true
% 2.33/0.98  --inst_learning_loop_flag               true
% 2.33/0.98  --inst_learning_start                   3000
% 2.33/0.98  --inst_learning_factor                  2
% 2.33/0.98  --inst_start_prop_sim_after_learn       3
% 2.33/0.98  --inst_sel_renew                        solver
% 2.33/0.98  --inst_lit_activity_flag                true
% 2.33/0.98  --inst_restr_to_given                   false
% 2.33/0.98  --inst_activity_threshold               500
% 2.33/0.98  --inst_out_proof                        true
% 2.33/0.98  
% 2.33/0.98  ------ Resolution Options
% 2.33/0.98  
% 2.33/0.98  --resolution_flag                       false
% 2.33/0.98  --res_lit_sel                           adaptive
% 2.33/0.98  --res_lit_sel_side                      none
% 2.33/0.98  --res_ordering                          kbo
% 2.33/0.98  --res_to_prop_solver                    active
% 2.33/0.98  --res_prop_simpl_new                    false
% 2.33/0.98  --res_prop_simpl_given                  true
% 2.33/0.98  --res_passive_queue_type                priority_queues
% 2.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.98  --res_passive_queues_freq               [15;5]
% 2.33/0.98  --res_forward_subs                      full
% 2.33/0.98  --res_backward_subs                     full
% 2.33/0.98  --res_forward_subs_resolution           true
% 2.33/0.98  --res_backward_subs_resolution          true
% 2.33/0.98  --res_orphan_elimination                true
% 2.33/0.98  --res_time_limit                        2.
% 2.33/0.98  --res_out_proof                         true
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Options
% 2.33/0.98  
% 2.33/0.98  --superposition_flag                    true
% 2.33/0.98  --sup_passive_queue_type                priority_queues
% 2.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.98  --demod_completeness_check              fast
% 2.33/0.98  --demod_use_ground                      true
% 2.33/0.98  --sup_to_prop_solver                    passive
% 2.33/0.98  --sup_prop_simpl_new                    true
% 2.33/0.98  --sup_prop_simpl_given                  true
% 2.33/0.98  --sup_fun_splitting                     false
% 2.33/0.98  --sup_smt_interval                      50000
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Simplification Setup
% 2.33/0.98  
% 2.33/0.98  --sup_indices_passive                   []
% 2.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_full_bw                           [BwDemod]
% 2.33/0.98  --sup_immed_triv                        [TrivRules]
% 2.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_immed_bw_main                     []
% 2.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  
% 2.33/0.98  ------ Combination Options
% 2.33/0.98  
% 2.33/0.98  --comb_res_mult                         3
% 2.33/0.98  --comb_sup_mult                         2
% 2.33/0.98  --comb_inst_mult                        10
% 2.33/0.98  
% 2.33/0.98  ------ Debug Options
% 2.33/0.98  
% 2.33/0.98  --dbg_backtrace                         false
% 2.33/0.98  --dbg_dump_prop_clauses                 false
% 2.33/0.98  --dbg_dump_prop_clauses_file            -
% 2.33/0.98  --dbg_out_stat                          false
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  ------ Proving...
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  % SZS status Theorem for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  fof(f12,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f32,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f12])).
% 2.33/0.98  
% 2.33/0.98  fof(f33,plain,(
% 2.33/0.98    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(flattening,[],[f32])).
% 2.33/0.98  
% 2.33/0.98  fof(f59,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f33])).
% 2.33/0.98  
% 2.33/0.98  fof(f1,axiom,(
% 2.33/0.98    v1_xboole_0(k1_xboole_0)),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f44,plain,(
% 2.33/0.98    v1_xboole_0(k1_xboole_0)),
% 2.33/0.98    inference(cnf_transformation,[],[f1])).
% 2.33/0.98  
% 2.33/0.98  fof(f13,axiom,(
% 2.33/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f34,plain,(
% 2.33/0.98    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.33/0.98    inference(ennf_transformation,[],[f13])).
% 2.33/0.98  
% 2.33/0.98  fof(f60,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f34])).
% 2.33/0.98  
% 2.33/0.98  fof(f16,conjecture,(
% 2.33/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f17,negated_conjecture,(
% 2.33/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.33/0.98    inference(negated_conjecture,[],[f16])).
% 2.33/0.98  
% 2.33/0.98  fof(f39,plain,(
% 2.33/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.33/0.98    inference(ennf_transformation,[],[f17])).
% 2.33/0.98  
% 2.33/0.98  fof(f40,plain,(
% 2.33/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.33/0.98    inference(flattening,[],[f39])).
% 2.33/0.98  
% 2.33/0.98  fof(f42,plain,(
% 2.33/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f43,plain,(
% 2.33/0.98    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f42])).
% 2.33/0.98  
% 2.33/0.98  fof(f75,plain,(
% 2.33/0.98    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.33/0.98    inference(cnf_transformation,[],[f43])).
% 2.33/0.98  
% 2.33/0.98  fof(f70,plain,(
% 2.33/0.98    v1_funct_1(sK2)),
% 2.33/0.98    inference(cnf_transformation,[],[f43])).
% 2.33/0.98  
% 2.33/0.98  fof(f72,plain,(
% 2.33/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.33/0.98    inference(cnf_transformation,[],[f43])).
% 2.33/0.98  
% 2.33/0.98  fof(f4,axiom,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f21,plain,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f4])).
% 2.33/0.98  
% 2.33/0.98  fof(f22,plain,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.98    inference(flattening,[],[f21])).
% 2.33/0.98  
% 2.33/0.98  fof(f48,plain,(
% 2.33/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f22])).
% 2.33/0.98  
% 2.33/0.98  fof(f7,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f27,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f7])).
% 2.33/0.98  
% 2.33/0.98  fof(f53,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f27])).
% 2.33/0.98  
% 2.33/0.98  fof(f14,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f35,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f14])).
% 2.33/0.98  
% 2.33/0.98  fof(f36,plain,(
% 2.33/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(flattening,[],[f35])).
% 2.33/0.98  
% 2.33/0.98  fof(f41,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(nnf_transformation,[],[f36])).
% 2.33/0.98  
% 2.33/0.98  fof(f61,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f41])).
% 2.33/0.98  
% 2.33/0.98  fof(f71,plain,(
% 2.33/0.98    v1_funct_2(sK2,sK0,sK1)),
% 2.33/0.98    inference(cnf_transformation,[],[f43])).
% 2.33/0.98  
% 2.33/0.98  fof(f9,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f29,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f9])).
% 2.33/0.98  
% 2.33/0.98  fof(f55,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f29])).
% 2.33/0.98  
% 2.33/0.98  fof(f15,axiom,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f37,plain,(
% 2.33/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f15])).
% 2.33/0.98  
% 2.33/0.98  fof(f38,plain,(
% 2.33/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.98    inference(flattening,[],[f37])).
% 2.33/0.98  
% 2.33/0.98  fof(f68,plain,(
% 2.33/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f38])).
% 2.33/0.98  
% 2.33/0.98  fof(f3,axiom,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f19,plain,(
% 2.33/0.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f3])).
% 2.33/0.98  
% 2.33/0.98  fof(f20,plain,(
% 2.33/0.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.98    inference(flattening,[],[f19])).
% 2.33/0.98  
% 2.33/0.98  fof(f46,plain,(
% 2.33/0.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f20])).
% 2.33/0.98  
% 2.33/0.98  fof(f73,plain,(
% 2.33/0.98    v2_funct_1(sK2)),
% 2.33/0.98    inference(cnf_transformation,[],[f43])).
% 2.33/0.98  
% 2.33/0.98  fof(f6,axiom,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f25,plain,(
% 2.33/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f6])).
% 2.33/0.98  
% 2.33/0.98  fof(f26,plain,(
% 2.33/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.98    inference(flattening,[],[f25])).
% 2.33/0.98  
% 2.33/0.98  fof(f52,plain,(
% 2.33/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f26])).
% 2.33/0.98  
% 2.33/0.98  fof(f10,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f30,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f10])).
% 2.33/0.98  
% 2.33/0.98  fof(f56,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f30])).
% 2.33/0.98  
% 2.33/0.98  fof(f74,plain,(
% 2.33/0.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.33/0.98    inference(cnf_transformation,[],[f43])).
% 2.33/0.98  
% 2.33/0.98  fof(f51,plain,(
% 2.33/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f26])).
% 2.33/0.98  
% 2.33/0.98  fof(f11,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f31,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f11])).
% 2.33/0.98  
% 2.33/0.98  fof(f57,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f31])).
% 2.33/0.98  
% 2.33/0.98  fof(f8,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f28,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f8])).
% 2.33/0.98  
% 2.33/0.98  fof(f54,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f28])).
% 2.33/0.98  
% 2.33/0.98  fof(f69,plain,(
% 2.33/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f38])).
% 2.33/0.98  
% 2.33/0.98  fof(f5,axiom,(
% 2.33/0.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f23,plain,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f5])).
% 2.33/0.98  
% 2.33/0.98  fof(f24,plain,(
% 2.33/0.98    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.98    inference(flattening,[],[f23])).
% 2.33/0.98  
% 2.33/0.98  fof(f50,plain,(
% 2.33/0.98    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f24])).
% 2.33/0.98  
% 2.33/0.98  fof(f2,axiom,(
% 2.33/0.98    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f18,plain,(
% 2.33/0.98    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.33/0.98    inference(ennf_transformation,[],[f2])).
% 2.33/0.98  
% 2.33/0.98  fof(f45,plain,(
% 2.33/0.98    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f18])).
% 2.33/0.98  
% 2.33/0.98  cnf(c_14,plain,
% 2.33/0.98      ( v1_funct_2(X0,X1,X2)
% 2.33/0.98      | ~ v1_partfun1(X0,X1)
% 2.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | ~ v1_funct_1(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_0,plain,
% 2.33/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_16,plain,
% 2.33/0.98      ( v1_partfun1(X0,X1)
% 2.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | ~ v1_xboole_0(X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_338,plain,
% 2.33/0.98      ( v1_partfun1(X0,X1)
% 2.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | k1_xboole_0 != X1 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_339,plain,
% 2.33/0.98      ( v1_partfun1(X0,k1_xboole_0)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_338]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_353,plain,
% 2.33/0.99      ( v1_funct_2(X0,X1,X2)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.33/0.99      | ~ v1_funct_1(X0)
% 2.33/0.99      | X3 != X0
% 2.33/0.99      | k1_xboole_0 != X1 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_339]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_354,plain,
% 2.33/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.33/0.99      | ~ v1_funct_1(X0) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_26,negated_conjecture,
% 2.33/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.33/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.33/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_619,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.33/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | k2_funct_1(sK2) != X0
% 2.33/0.99      | sK0 != X1
% 2.33/0.99      | sK1 != k1_xboole_0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_354,c_26]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_620,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.33/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | sK1 != k1_xboole_0 ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_619]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_962,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
% 2.33/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | sK1 != k1_xboole_0 ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_620]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_988,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | sP0_iProver_split
% 2.33/0.99      | sK1 != k1_xboole_0 ),
% 2.33/0.99      inference(splitting,
% 2.33/0.99                [splitting(split),new_symbols(definition,[])],
% 2.33/0.99                [c_962]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1509,plain,
% 2.33/0.99      ( sK1 != k1_xboole_0
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.33/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.33/0.99      | sP0_iProver_split = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_988]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_987,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48)))
% 2.33/0.99      | ~ sP0_iProver_split ),
% 2.33/0.99      inference(splitting,
% 2.33/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.33/0.99                [c_962]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1510,plain,
% 2.33/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48))) != iProver_top
% 2.33/0.99      | sP0_iProver_split != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1664,plain,
% 2.33/0.99      ( sK1 != k1_xboole_0
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.33/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/0.99      inference(forward_subsumption_resolution,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_1509,c_1510]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_31,negated_conjecture,
% 2.33/0.99      ( v1_funct_1(sK2) ),
% 2.33/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_32,plain,
% 2.33/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_29,negated_conjecture,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.33/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_34,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1054,plain,
% 2.33/0.99      ( sK1 != k1_xboole_0
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.33/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.33/0.99      | sP0_iProver_split = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_988]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.33/0.99      | ~ v1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_985,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0_48)
% 2.33/0.99      | v1_funct_1(k2_funct_1(X0_48))
% 2.33/0.99      | ~ v1_relat_1(X0_48) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1749,plain,
% 2.33/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | ~ v1_funct_1(sK2)
% 2.33/0.99      | ~ v1_relat_1(sK2) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_985]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1750,plain,
% 2.33/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.33/0.99      | v1_funct_1(sK2) != iProver_top
% 2.33/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_9,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | v1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_983,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.99      | v1_relat_1(X0_48) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1752,plain,
% 2.33/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.33/0.99      | v1_relat_1(sK2) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_983]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1753,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.33/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1752]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_22,plain,
% 2.33/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.33/0.99      | k1_xboole_0 = X2 ),
% 2.33/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_30,negated_conjecture,
% 2.33/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_513,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.33/0.99      | sK0 != X1
% 2.33/0.99      | sK1 != X2
% 2.33/0.99      | sK2 != X0
% 2.33/0.99      | k1_xboole_0 = X2 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_514,plain,
% 2.33/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.33/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.33/0.99      | k1_xboole_0 = sK1 ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_513]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_516,plain,
% 2.33/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_514,c_29]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_967,plain,
% 2.33/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_516]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_976,negated_conjecture,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_29]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1496,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_976]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_11,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_981,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.99      | k1_relset_1(X1_48,X2_48,X0_48) = k1_relat_1(X0_48) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1492,plain,
% 2.33/0.99      ( k1_relset_1(X0_48,X1_48,X2_48) = k1_relat_1(X2_48)
% 2.33/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1994,plain,
% 2.33/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_1496,c_1492]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2071,plain,
% 2.33/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_967,c_1994]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_24,plain,
% 2.33/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.33/0.99      | ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_672,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k1_relat_1(X0) != sK1
% 2.33/0.99      | k2_relat_1(X0) != sK0
% 2.33/0.99      | k2_funct_1(sK2) != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_673,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.33/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_672]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_685,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.33/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_673,c_9]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_959,plain,
% 2.33/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_685]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1513,plain,
% 2.33/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1060,plain,
% 2.33/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3432,plain,
% 2.33/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.33/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_1513,c_32,c_34,c_1060,c_1750,c_1753]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3433,plain,
% 2.33/0.99      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_3432]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v2_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_28,negated_conjecture,
% 2.33/0.99      ( v2_funct_1(sK2) ),
% 2.33/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_418,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.33/0.99      | sK2 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_28]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_419,plain,
% 2.33/0.99      ( ~ v1_funct_1(sK2)
% 2.33/0.99      | ~ v1_relat_1(sK2)
% 2.33/0.99      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_421,plain,
% 2.33/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_419,c_31]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_971,plain,
% 2.33/0.99      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_421]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1501,plain,
% 2.33/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.33/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1767,plain,
% 2.33/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_1501,c_29,c_971,c_1752]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_7,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v2_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_390,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.33/0.99      | sK2 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_391,plain,
% 2.33/0.99      ( ~ v1_funct_1(sK2)
% 2.33/0.99      | ~ v1_relat_1(sK2)
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_393,plain,
% 2.33/0.99      ( ~ v1_relat_1(sK2)
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_391,c_31]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_973,plain,
% 2.33/0.99      ( ~ v1_relat_1(sK2)
% 2.33/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_393]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1499,plain,
% 2.33/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.33/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1804,plain,
% 2.33/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_1499,c_29,c_973,c_1752]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1806,plain,
% 2.33/0.99      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_1804,c_1767]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_12,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_980,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.99      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1493,plain,
% 2.33/0.99      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.33/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2420,plain,
% 2.33/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_1496,c_1493]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_27,negated_conjecture,
% 2.33/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.33/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_977,negated_conjecture,
% 2.33/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2427,plain,
% 2.33/0.99      ( k2_relat_1(sK2) = sK1 ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_2420,c_977]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_8,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v2_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_376,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.33/0.99      | sK2 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_28]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_377,plain,
% 2.33/0.99      ( ~ v1_funct_1(sK2)
% 2.33/0.99      | ~ v1_relat_1(sK2)
% 2.33/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_376]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_379,plain,
% 2.33/0.99      ( ~ v1_relat_1(sK2)
% 2.33/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_377,c_31]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_974,plain,
% 2.33/0.99      ( ~ v1_relat_1(sK2)
% 2.33/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_379]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1498,plain,
% 2.33/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.33/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_974]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1799,plain,
% 2.33/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_1498,c_29,c_974,c_1752]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1801,plain,
% 2.33/0.99      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_1799,c_1767]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2433,plain,
% 2.33/0.99      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 2.33/0.99      inference(demodulation,[status(thm)],[c_2427,c_1801]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3436,plain,
% 2.33/0.99      ( k1_relat_1(sK2) != sK0
% 2.33/0.99      | sK1 != sK1
% 2.33/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.33/0.99      inference(light_normalisation,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_3433,c_1767,c_1806,c_2433]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3437,plain,
% 2.33/0.99      ( k1_relat_1(sK2) != sK0
% 2.33/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.33/0.99      inference(equality_resolution_simp,[status(thm)],[c_3436]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_13,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_979,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.99      | k3_relset_1(X1_48,X2_48,X0_48) = k4_relat_1(X0_48) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1494,plain,
% 2.33/0.99      ( k3_relset_1(X0_48,X1_48,X2_48) = k4_relat_1(X2_48)
% 2.33/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_979]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2527,plain,
% 2.33/0.99      ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_1496,c_1494]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_10,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.33/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_982,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.99      | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1491,plain,
% 2.33/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.33/0.99      | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2692,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 2.33/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2527,c_1491]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2847,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_2692,c_34]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3440,plain,
% 2.33/0.99      ( k1_relat_1(sK2) != sK0 ),
% 2.33/0.99      inference(forward_subsumption_resolution,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_3437,c_2847]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_23,plain,
% 2.33/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.33/0.99      | ~ v1_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_978,plain,
% 2.33/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_48),k2_relat_1(X0_48))))
% 2.33/0.99      | ~ v1_funct_1(X0_48)
% 2.33/0.99      | ~ v1_relat_1(X0_48) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1495,plain,
% 2.33/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_48),k2_relat_1(X0_48)))) = iProver_top
% 2.33/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.33/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2543,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
% 2.33/0.99      | v1_funct_1(sK2) != iProver_top
% 2.33/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2427,c_1495]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2744,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_2543,c_32,c_34,c_1753]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2751,plain,
% 2.33/0.99      ( k3_relset_1(k1_relat_1(sK2),sK1,sK2) = k4_relat_1(sK2) ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2744,c_1494]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2800,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.33/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2751,c_1491]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | v1_funct_1(k4_relat_1(X0))
% 2.33/0.99      | ~ v2_funct_1(X0)
% 2.33/0.99      | ~ v1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_404,plain,
% 2.33/0.99      ( ~ v1_funct_1(X0)
% 2.33/0.99      | v1_funct_1(k4_relat_1(X0))
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | sK2 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_405,plain,
% 2.33/0.99      ( v1_funct_1(k4_relat_1(sK2))
% 2.33/0.99      | ~ v1_funct_1(sK2)
% 2.33/0.99      | ~ v1_relat_1(sK2) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_404]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_406,plain,
% 2.33/0.99      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.33/0.99      | v1_funct_1(sK2) != iProver_top
% 2.33/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1,plain,
% 2.33/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 2.33/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_986,plain,
% 2.33/0.99      ( ~ v1_relat_1(X0_48) | v1_relat_1(k4_relat_1(X0_48)) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1813,plain,
% 2.33/0.99      ( v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_986]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1819,plain,
% 2.33/0.99      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 2.33/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2688,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k4_relat_1(sK2))))) = iProver_top
% 2.33/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.33/0.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2433,c_1495]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2689,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.33/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.33/0.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_2688,c_1806]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3955,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_2800,c_32,c_34,c_406,c_1753,c_1819,c_2689]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3441,plain,
% 2.33/0.99      ( sK1 = k1_xboole_0 ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2071,c_3440]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3959,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_3955,c_3441]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2074,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_48))) != iProver_top
% 2.33/0.99      | sP0_iProver_split != iProver_top ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_1510,c_1767]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3969,plain,
% 2.33/0.99      ( sP0_iProver_split != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_3959,c_2074]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4154,plain,
% 2.33/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_1664,c_32,c_34,c_1054,c_1750,c_1753,c_2071,c_3440,
% 2.33/0.99                 c_3969]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4155,plain,
% 2.33/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_4154]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4158,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_4155,c_1767,c_3441]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3445,plain,
% 2.33/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
% 2.33/0.99      inference(demodulation,[status(thm)],[c_3441,c_2847]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(contradiction,plain,
% 2.33/0.99      ( $false ),
% 2.33/0.99      inference(minisat,[status(thm)],[c_4158,c_3445]) ).
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  ------                               Statistics
% 2.33/0.99  
% 2.33/0.99  ------ General
% 2.33/0.99  
% 2.33/0.99  abstr_ref_over_cycles:                  0
% 2.33/0.99  abstr_ref_under_cycles:                 0
% 2.33/0.99  gc_basic_clause_elim:                   0
% 2.33/0.99  forced_gc_time:                         0
% 2.33/0.99  parsing_time:                           0.009
% 2.33/0.99  unif_index_cands_time:                  0.
% 2.33/0.99  unif_index_add_time:                    0.
% 2.33/0.99  orderings_time:                         0.
% 2.33/0.99  out_proof_time:                         0.017
% 2.33/0.99  total_time:                             0.165
% 2.33/0.99  num_of_symbols:                         52
% 2.33/0.99  num_of_terms:                           3362
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing
% 2.33/0.99  
% 2.33/0.99  num_of_splits:                          1
% 2.33/0.99  num_of_split_atoms:                     1
% 2.33/0.99  num_of_reused_defs:                     0
% 2.33/0.99  num_eq_ax_congr_red:                    14
% 2.33/0.99  num_of_sem_filtered_clauses:            1
% 2.33/0.99  num_of_subtypes:                        3
% 2.33/0.99  monotx_restored_types:                  0
% 2.33/0.99  sat_num_of_epr_types:                   0
% 2.33/0.99  sat_num_of_non_cyclic_types:            0
% 2.33/0.99  sat_guarded_non_collapsed_types:        1
% 2.33/0.99  num_pure_diseq_elim:                    0
% 2.33/0.99  simp_replaced_by:                       0
% 2.33/0.99  res_preprocessed:                       149
% 2.33/0.99  prep_upred:                             0
% 2.33/0.99  prep_unflattend:                        56
% 2.33/0.99  smt_new_axioms:                         0
% 2.33/0.99  pred_elim_cands:                        3
% 2.33/0.99  pred_elim:                              4
% 2.33/0.99  pred_elim_cl:                           0
% 2.33/0.99  pred_elim_cycles:                       6
% 2.33/0.99  merged_defs:                            0
% 2.33/0.99  merged_defs_ncl:                        0
% 2.33/0.99  bin_hyper_res:                          0
% 2.33/0.99  prep_cycles:                            4
% 2.33/0.99  pred_elim_time:                         0.01
% 2.33/0.99  splitting_time:                         0.
% 2.33/0.99  sem_filter_time:                        0.
% 2.33/0.99  monotx_time:                            0.
% 2.33/0.99  subtype_inf_time:                       0.001
% 2.33/0.99  
% 2.33/0.99  ------ Problem properties
% 2.33/0.99  
% 2.33/0.99  clauses:                                30
% 2.33/0.99  conjectures:                            3
% 2.33/0.99  epr:                                    1
% 2.33/0.99  horn:                                   26
% 2.33/0.99  ground:                                 16
% 2.33/0.99  unary:                                  3
% 2.33/0.99  binary:                                 12
% 2.33/0.99  lits:                                   88
% 2.33/0.99  lits_eq:                                34
% 2.33/0.99  fd_pure:                                0
% 2.33/0.99  fd_pseudo:                              0
% 2.33/0.99  fd_cond:                                1
% 2.33/0.99  fd_pseudo_cond:                         0
% 2.33/0.99  ac_symbols:                             0
% 2.33/0.99  
% 2.33/0.99  ------ Propositional Solver
% 2.33/0.99  
% 2.33/0.99  prop_solver_calls:                      27
% 2.33/0.99  prop_fast_solver_calls:                 1089
% 2.33/0.99  smt_solver_calls:                       0
% 2.33/0.99  smt_fast_solver_calls:                  0
% 2.33/0.99  prop_num_of_clauses:                    1511
% 2.33/0.99  prop_preprocess_simplified:             5214
% 2.33/0.99  prop_fo_subsumed:                       24
% 2.33/0.99  prop_solver_time:                       0.
% 2.33/0.99  smt_solver_time:                        0.
% 2.33/0.99  smt_fast_solver_time:                   0.
% 2.33/0.99  prop_fast_solver_time:                  0.
% 2.33/0.99  prop_unsat_core_time:                   0.
% 2.33/0.99  
% 2.33/0.99  ------ QBF
% 2.33/0.99  
% 2.33/0.99  qbf_q_res:                              0
% 2.33/0.99  qbf_num_tautologies:                    0
% 2.33/0.99  qbf_prep_cycles:                        0
% 2.33/0.99  
% 2.33/0.99  ------ BMC1
% 2.33/0.99  
% 2.33/0.99  bmc1_current_bound:                     -1
% 2.33/0.99  bmc1_last_solved_bound:                 -1
% 2.33/0.99  bmc1_unsat_core_size:                   -1
% 2.33/0.99  bmc1_unsat_core_parents_size:           -1
% 2.33/0.99  bmc1_merge_next_fun:                    0
% 2.33/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation
% 2.33/0.99  
% 2.33/0.99  inst_num_of_clauses:                    513
% 2.33/0.99  inst_num_in_passive:                    119
% 2.33/0.99  inst_num_in_active:                     255
% 2.33/0.99  inst_num_in_unprocessed:                139
% 2.33/0.99  inst_num_of_loops:                      280
% 2.33/0.99  inst_num_of_learning_restarts:          0
% 2.33/0.99  inst_num_moves_active_passive:          23
% 2.33/0.99  inst_lit_activity:                      0
% 2.33/0.99  inst_lit_activity_moves:                0
% 2.33/0.99  inst_num_tautologies:                   0
% 2.33/0.99  inst_num_prop_implied:                  0
% 2.33/0.99  inst_num_existing_simplified:           0
% 2.33/0.99  inst_num_eq_res_simplified:             0
% 2.33/0.99  inst_num_child_elim:                    0
% 2.33/0.99  inst_num_of_dismatching_blockings:      10
% 2.33/0.99  inst_num_of_non_proper_insts:           230
% 2.33/0.99  inst_num_of_duplicates:                 0
% 2.33/0.99  inst_inst_num_from_inst_to_res:         0
% 2.33/0.99  inst_dismatching_checking_time:         0.
% 2.33/0.99  
% 2.33/0.99  ------ Resolution
% 2.33/0.99  
% 2.33/0.99  res_num_of_clauses:                     0
% 2.33/0.99  res_num_in_passive:                     0
% 2.33/0.99  res_num_in_active:                      0
% 2.33/0.99  res_num_of_loops:                       153
% 2.33/0.99  res_forward_subset_subsumed:            11
% 2.33/0.99  res_backward_subset_subsumed:           4
% 2.33/0.99  res_forward_subsumed:                   0
% 2.33/0.99  res_backward_subsumed:                  0
% 2.33/0.99  res_forward_subsumption_resolution:     3
% 2.33/0.99  res_backward_subsumption_resolution:    0
% 2.33/0.99  res_clause_to_clause_subsumption:       135
% 2.33/0.99  res_orphan_elimination:                 0
% 2.33/0.99  res_tautology_del:                      37
% 2.33/0.99  res_num_eq_res_simplified:              0
% 2.33/0.99  res_num_sel_changes:                    0
% 2.33/0.99  res_moves_from_active_to_pass:          0
% 2.33/0.99  
% 2.33/0.99  ------ Superposition
% 2.33/0.99  
% 2.33/0.99  sup_time_total:                         0.
% 2.33/0.99  sup_time_generating:                    0.
% 2.33/0.99  sup_time_sim_full:                      0.
% 2.33/0.99  sup_time_sim_immed:                     0.
% 2.33/0.99  
% 2.33/0.99  sup_num_of_clauses:                     67
% 2.33/0.99  sup_num_in_active:                      35
% 2.33/0.99  sup_num_in_passive:                     32
% 2.33/0.99  sup_num_of_loops:                       55
% 2.33/0.99  sup_fw_superposition:                   38
% 2.33/0.99  sup_bw_superposition:                   40
% 2.33/0.99  sup_immediate_simplified:               39
% 2.33/0.99  sup_given_eliminated:                   0
% 2.33/0.99  comparisons_done:                       0
% 2.33/0.99  comparisons_avoided:                    5
% 2.33/0.99  
% 2.33/0.99  ------ Simplifications
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  sim_fw_subset_subsumed:                 14
% 2.33/0.99  sim_bw_subset_subsumed:                 5
% 2.33/0.99  sim_fw_subsumed:                        2
% 2.33/0.99  sim_bw_subsumed:                        0
% 2.33/0.99  sim_fw_subsumption_res:                 3
% 2.33/0.99  sim_bw_subsumption_res:                 1
% 2.33/0.99  sim_tautology_del:                      1
% 2.33/0.99  sim_eq_tautology_del:                   5
% 2.33/0.99  sim_eq_res_simp:                        2
% 2.33/0.99  sim_fw_demodulated:                     0
% 2.33/0.99  sim_bw_demodulated:                     20
% 2.33/0.99  sim_light_normalised:                   32
% 2.33/0.99  sim_joinable_taut:                      0
% 2.33/0.99  sim_joinable_simp:                      0
% 2.33/0.99  sim_ac_normalised:                      0
% 2.33/0.99  sim_smt_subsumption:                    0
% 2.33/0.99  
%------------------------------------------------------------------------------
